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
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 466 expanded)
%              Number of leaves         :   41 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  593 (1325 expanded)
%              Number of equality atoms :  119 ( 314 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10799)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f1023,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f391,f394,f414,f447,f466,f485,f503,f521,f651,f659,f668,f693,f712,f1022])).

fof(f1022,plain,
    ( spl8_19
    | ~ spl8_33
    | ~ spl8_38 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | spl8_19
    | ~ spl8_33
    | ~ spl8_38 ),
    inference(resolution,[],[f857,f171])).

fof(f171,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f139,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f136,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK5(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f89,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f857,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)))
    | spl8_19
    | ~ spl8_33
    | ~ spl8_38 ),
    inference(backward_demodulation,[],[f726,f854])).

fof(f854,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_33
    | ~ spl8_38 ),
    inference(resolution,[],[f757,f174])).

fof(f174,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f171,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f757,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ spl8_33
    | ~ spl8_38 ),
    inference(backward_demodulation,[],[f662,f688])).

fof(f688,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl8_38
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f662,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK4),X0)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl8_33
  <=> ! [X0] : r1_tarski(k2_relat_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f726,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)))
    | spl8_19
    | ~ spl8_38 ),
    inference(backward_demodulation,[],[f413,f688])).

fof(f413,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl8_19
  <=> r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f712,plain,(
    spl8_39 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | spl8_39 ),
    inference(resolution,[],[f692,f171])).

fof(f692,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl8_39
  <=> r1_tarski(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f693,plain,
    ( spl8_38
    | ~ spl8_39
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f657,f500,f690,f686])).

fof(f500,plain,
    ( spl8_28
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f657,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4
    | ~ spl8_28 ),
    inference(resolution,[],[f502,f146])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f87,f95])).

fof(f502,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f500])).

fof(f668,plain,
    ( spl8_33
    | ~ spl8_28
    | ~ spl8_18
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f601,f463,f407,f500,f661])).

fof(f407,plain,
    ( spl8_18
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f463,plain,
    ( spl8_23
  <=> ! [X1] :
        ( k2_relat_1(sK4) = k11_relat_1(sK4,X1)
        | ~ v4_relat_1(sK4,k2_enumset1(X1,X1,X1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(k2_relat_1(sK4),X0) )
    | ~ spl8_18
    | ~ spl8_23 ),
    inference(superposition,[],[f595,f129])).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f595,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK5(k2_relat_1(sK4),X3))))
        | r1_tarski(k2_relat_1(sK4),X3) )
    | ~ spl8_18
    | ~ spl8_23 ),
    inference(resolution,[],[f593,f139])).

fof(f593,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_18
    | ~ spl8_23 ),
    inference(superposition,[],[f589,f544])).

fof(f544,plain,
    ( k2_relat_1(sK4) = k11_relat_1(sK4,sK1)
    | ~ spl8_23 ),
    inference(resolution,[],[f474,f115])).

fof(f115,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f70,f113])).

fof(f113,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f474,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)))
        | k2_relat_1(sK4) = k11_relat_1(sK4,X0) )
    | ~ spl8_23 ),
    inference(resolution,[],[f464,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f464,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK4,k2_enumset1(X1,X1,X1,X1))
        | k2_relat_1(sK4) = k11_relat_1(sK4,X1) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f463])).

fof(f589,plain,
    ( ! [X6,X4,X5] :
        ( m1_subset_1(k11_relat_1(sK4,X4),k1_zfmisc_1(X5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) )
    | ~ spl8_18 ),
    inference(superposition,[],[f377,f456])).

fof(f456,plain,
    ( ! [X0] : k11_relat_1(sK4,X0) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0))
    | ~ spl8_18 ),
    inference(resolution,[],[f408,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f75,f113])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f408,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f407])).

fof(f377,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f110,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f659,plain,
    ( spl8_17
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl8_17
    | ~ spl8_28 ),
    inference(resolution,[],[f502,f441])).

fof(f441,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | spl8_17 ),
    inference(superposition,[],[f416,f128])).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f416,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | spl8_17 ),
    inference(resolution,[],[f405,f102])).

fof(f405,plain,
    ( ~ v4_relat_1(sK4,sK3)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl8_17
  <=> v4_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f651,plain,
    ( spl8_16
    | ~ spl8_18
    | ~ spl8_23
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | spl8_16
    | ~ spl8_18
    | ~ spl8_23
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(resolution,[],[f644,f408])).

fof(f644,plain,
    ( ~ v1_relat_1(sK4)
    | spl8_16
    | ~ spl8_18
    | ~ spl8_23
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(resolution,[],[f629,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f629,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | spl8_16
    | ~ spl8_18
    | ~ spl8_23
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f390,f625])).

fof(f625,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | ~ spl8_18
    | ~ spl8_23
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f621,f544])).

fof(f621,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1)
    | ~ spl8_18
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f534,f612])).

fof(f612,plain,
    ( sK1 = sK7(k1_relat_1(sK4),k1_xboole_0,sK4)
    | ~ spl8_18
    | ~ spl8_27 ),
    inference(resolution,[],[f609,f497])).

fof(f497,plain,
    ( r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl8_27
  <=> r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f609,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k1_relat_1(sK4))
        | sK1 = X7 )
    | ~ spl8_18 ),
    inference(resolution,[],[f197,f558])).

fof(f558,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f557,f115])).

fof(f557,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | r1_tarski(k1_relat_1(sK4),X10) )
    | ~ spl8_18 ),
    inference(resolution,[],[f167,f408])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f197,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X1,X1,X1,X1))
      | ~ r2_hidden(X2,X3)
      | X1 = X2 ) ),
    inference(resolution,[],[f127,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f91,f113])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f534,plain,
    ( k11_relat_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)) = k2_enumset1(k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)))
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(resolution,[],[f520,f497])).

fof(f520,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl8_29
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f390,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl8_16
  <=> r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f521,plain,
    ( ~ spl8_18
    | spl8_29 ),
    inference(avatar_split_clause,[],[f516,f519,f407])).

fof(f516,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0))
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f118,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f83,f113])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f503,plain,
    ( spl8_27
    | spl8_28
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f492,f483,f500,f495])).

fof(f483,plain,
    ( spl8_26
  <=> ! [X0] :
        ( r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
        | sP0(X0,k1_relat_1(sK4),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f492,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4))
    | ~ spl8_26 ),
    inference(superposition,[],[f486,f128])).

fof(f486,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
        | r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) )
    | ~ spl8_26 ),
    inference(resolution,[],[f484,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f484,plain,
    ( ! [X0] :
        ( sP0(X0,k1_relat_1(sK4),sK4)
        | r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f483])).

fof(f485,plain,
    ( ~ spl8_18
    | spl8_26 ),
    inference(avatar_split_clause,[],[f480,f483,f407])).

fof(f480,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
      | sP0(X0,k1_relat_1(sK4),sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f131,f68])).

fof(f131,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP0(X1,k1_relat_1(X2),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f41,f46])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f466,plain,
    ( ~ spl8_18
    | spl8_23
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f460,f407,f463,f407])).

fof(f460,plain,
    ( ! [X0] :
        ( k2_relat_1(sK4) = k11_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4)
        | ~ v4_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) )
    | ~ spl8_18 ),
    inference(superposition,[],[f184,f456])).

fof(f184,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f80,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f447,plain,(
    spl8_18 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl8_18 ),
    inference(resolution,[],[f418,f77])).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f418,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | spl8_18 ),
    inference(resolution,[],[f415,f115])).

fof(f415,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_18 ),
    inference(resolution,[],[f409,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f409,plain,
    ( ~ v1_relat_1(sK4)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f407])).

fof(f414,plain,
    ( ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | spl8_16 ),
    inference(avatar_split_clause,[],[f401,f388,f411,f407,f403])).

fof(f401,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ v1_relat_1(sK4)
    | ~ v4_relat_1(sK4,sK3)
    | spl8_16 ),
    inference(superposition,[],[f390,f184])).

fof(f394,plain,(
    spl8_14 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl8_14 ),
    inference(resolution,[],[f381,f115])).

fof(f381,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl8_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f391,plain,
    ( ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f375,f388,f379])).

fof(f375,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(superposition,[],[f114,f111])).

fof(f114,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f72,f113,f113])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (10790)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.52  % (10788)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (10807)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.54  % (10792)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (10787)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.55  % (10809)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (10795)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (10783)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.55  % (10785)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.56  % (10798)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.56  % (10793)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.56  % (10785)Refutation not found, incomplete strategy% (10785)------------------------------
% 1.42/0.56  % (10785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (10785)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (10785)Memory used [KB]: 10874
% 1.42/0.56  % (10804)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.56  % (10785)Time elapsed: 0.144 s
% 1.42/0.56  % (10785)------------------------------
% 1.42/0.56  % (10785)------------------------------
% 1.42/0.56  % (10811)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.56  % (10805)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (10801)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.56  % (10800)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (10805)Refutation not found, incomplete strategy% (10805)------------------------------
% 1.42/0.56  % (10805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (10805)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (10805)Memory used [KB]: 1791
% 1.42/0.56  % (10805)Time elapsed: 0.149 s
% 1.42/0.56  % (10805)------------------------------
% 1.42/0.56  % (10805)------------------------------
% 1.42/0.57  % (10810)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.57  % (10803)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.57  % (10786)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.57  % (10813)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.57  % (10806)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.57  % (10794)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.58  % (10796)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.58  % (10791)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.58  % (10802)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.58  % (10804)Refutation not found, incomplete strategy% (10804)------------------------------
% 1.42/0.58  % (10804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (10804)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (10804)Memory used [KB]: 10746
% 1.42/0.58  % (10804)Time elapsed: 0.176 s
% 1.42/0.58  % (10804)------------------------------
% 1.42/0.58  % (10804)------------------------------
% 1.42/0.58  % (10784)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.59  % (10808)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.59  % (10795)Refutation found. Thanks to Tanya!
% 1.42/0.59  % SZS status Theorem for theBenchmark
% 1.42/0.60  % (10789)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.60  % SZS output start Proof for theBenchmark
% 1.42/0.60  % (10799)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.60  fof(f1023,plain,(
% 1.42/0.60    $false),
% 1.42/0.60    inference(avatar_sat_refutation,[],[f391,f394,f414,f447,f466,f485,f503,f521,f651,f659,f668,f693,f712,f1022])).
% 1.42/0.60  fof(f1022,plain,(
% 1.42/0.60    spl8_19 | ~spl8_33 | ~spl8_38),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f1020])).
% 1.42/0.60  fof(f1020,plain,(
% 1.42/0.60    $false | (spl8_19 | ~spl8_33 | ~spl8_38)),
% 1.42/0.60    inference(resolution,[],[f857,f171])).
% 1.42/0.60  fof(f171,plain,(
% 1.42/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.60    inference(resolution,[],[f139,f73])).
% 1.42/0.60  fof(f73,plain,(
% 1.42/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f8])).
% 1.42/0.60  fof(f8,axiom,(
% 1.42/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.42/0.60  fof(f139,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK5(X0,X1))) | r1_tarski(X0,X1)) )),
% 1.42/0.60    inference(resolution,[],[f136,f95])).
% 1.42/0.60  fof(f95,plain,(
% 1.42/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f61])).
% 1.42/0.60  fof(f61,plain,(
% 1.42/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/0.60    inference(nnf_transformation,[],[f9])).
% 1.42/0.60  fof(f9,axiom,(
% 1.42/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.60  fof(f136,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~r1_tarski(X0,sK5(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.42/0.60    inference(resolution,[],[f89,f100])).
% 1.42/0.60  fof(f100,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f38])).
% 1.42/0.60  fof(f38,plain,(
% 1.42/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f19])).
% 1.42/0.60  fof(f19,axiom,(
% 1.42/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.42/0.60  fof(f89,plain,(
% 1.42/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f56])).
% 1.42/0.60  fof(f56,plain,(
% 1.42/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).
% 1.42/0.60  fof(f55,plain,(
% 1.42/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.42/0.60    introduced(choice_axiom,[])).
% 1.42/0.60  fof(f54,plain,(
% 1.42/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.60    inference(rectify,[],[f53])).
% 1.42/0.60  fof(f53,plain,(
% 1.42/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.60    inference(nnf_transformation,[],[f37])).
% 1.42/0.60  fof(f37,plain,(
% 1.42/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.60    inference(ennf_transformation,[],[f1])).
% 1.42/0.60  fof(f1,axiom,(
% 1.42/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.60  fof(f857,plain,(
% 1.42/0.60    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) | (spl8_19 | ~spl8_33 | ~spl8_38)),
% 1.42/0.60    inference(backward_demodulation,[],[f726,f854])).
% 1.42/0.60  fof(f854,plain,(
% 1.42/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl8_33 | ~spl8_38)),
% 1.42/0.60    inference(resolution,[],[f757,f174])).
% 1.42/0.60  fof(f174,plain,(
% 1.42/0.60    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.42/0.60    inference(resolution,[],[f171,f87])).
% 1.42/0.60  fof(f87,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f52])).
% 1.42/0.60  fof(f52,plain,(
% 1.42/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.60    inference(flattening,[],[f51])).
% 1.42/0.60  fof(f51,plain,(
% 1.42/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.60    inference(nnf_transformation,[],[f2])).
% 1.42/0.60  fof(f2,axiom,(
% 1.42/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.60  fof(f757,plain,(
% 1.42/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) ) | (~spl8_33 | ~spl8_38)),
% 1.42/0.60    inference(backward_demodulation,[],[f662,f688])).
% 1.42/0.60  fof(f688,plain,(
% 1.42/0.60    k1_xboole_0 = sK4 | ~spl8_38),
% 1.42/0.60    inference(avatar_component_clause,[],[f686])).
% 1.42/0.60  fof(f686,plain,(
% 1.42/0.60    spl8_38 <=> k1_xboole_0 = sK4),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.42/0.60  fof(f662,plain,(
% 1.42/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0)) ) | ~spl8_33),
% 1.42/0.60    inference(avatar_component_clause,[],[f661])).
% 1.42/0.60  fof(f661,plain,(
% 1.42/0.60    spl8_33 <=> ! [X0] : r1_tarski(k2_relat_1(sK4),X0)),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.42/0.60  fof(f726,plain,(
% 1.42/0.60    ~r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) | (spl8_19 | ~spl8_38)),
% 1.42/0.60    inference(backward_demodulation,[],[f413,f688])).
% 1.42/0.60  fof(f413,plain,(
% 1.42/0.60    ~r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) | spl8_19),
% 1.42/0.60    inference(avatar_component_clause,[],[f411])).
% 1.42/0.60  fof(f411,plain,(
% 1.42/0.60    spl8_19 <=> r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.42/0.60  fof(f712,plain,(
% 1.42/0.60    spl8_39),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f710])).
% 1.42/0.60  fof(f710,plain,(
% 1.42/0.60    $false | spl8_39),
% 1.42/0.60    inference(resolution,[],[f692,f171])).
% 1.42/0.60  fof(f692,plain,(
% 1.42/0.60    ~r1_tarski(k1_xboole_0,sK4) | spl8_39),
% 1.42/0.60    inference(avatar_component_clause,[],[f690])).
% 1.42/0.60  fof(f690,plain,(
% 1.42/0.60    spl8_39 <=> r1_tarski(k1_xboole_0,sK4)),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.42/0.60  fof(f693,plain,(
% 1.42/0.60    spl8_38 | ~spl8_39 | ~spl8_28),
% 1.42/0.60    inference(avatar_split_clause,[],[f657,f500,f690,f686])).
% 1.42/0.60  fof(f500,plain,(
% 1.42/0.60    spl8_28 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.42/0.60  fof(f657,plain,(
% 1.42/0.60    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 = sK4 | ~spl8_28),
% 1.42/0.60    inference(resolution,[],[f502,f146])).
% 1.42/0.60  fof(f146,plain,(
% 1.42/0.60    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 1.42/0.60    inference(resolution,[],[f87,f95])).
% 1.42/0.60  fof(f502,plain,(
% 1.42/0.60    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl8_28),
% 1.42/0.60    inference(avatar_component_clause,[],[f500])).
% 1.42/0.60  fof(f668,plain,(
% 1.42/0.60    spl8_33 | ~spl8_28 | ~spl8_18 | ~spl8_23),
% 1.42/0.60    inference(avatar_split_clause,[],[f601,f463,f407,f500,f661])).
% 1.42/0.60  fof(f407,plain,(
% 1.42/0.60    spl8_18 <=> v1_relat_1(sK4)),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.42/0.60  fof(f463,plain,(
% 1.42/0.60    spl8_23 <=> ! [X1] : (k2_relat_1(sK4) = k11_relat_1(sK4,X1) | ~v4_relat_1(sK4,k2_enumset1(X1,X1,X1,X1)))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.42/0.60  fof(f601,plain,(
% 1.42/0.60    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK4),X0)) ) | (~spl8_18 | ~spl8_23)),
% 1.42/0.60    inference(superposition,[],[f595,f129])).
% 1.42/0.60  fof(f129,plain,(
% 1.42/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.42/0.60    inference(equality_resolution,[],[f98])).
% 1.42/0.60  fof(f98,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.42/0.60    inference(cnf_transformation,[],[f63])).
% 1.42/0.60  fof(f63,plain,(
% 1.42/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.42/0.60    inference(flattening,[],[f62])).
% 1.42/0.60  fof(f62,plain,(
% 1.42/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.42/0.60    inference(nnf_transformation,[],[f7])).
% 1.42/0.60  fof(f7,axiom,(
% 1.42/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.42/0.60  fof(f595,plain,(
% 1.42/0.60    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK5(k2_relat_1(sK4),X3)))) | r1_tarski(k2_relat_1(sK4),X3)) ) | (~spl8_18 | ~spl8_23)),
% 1.42/0.60    inference(resolution,[],[f593,f139])).
% 1.42/0.60  fof(f593,plain,(
% 1.42/0.60    ( ! [X0,X1] : (m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl8_18 | ~spl8_23)),
% 1.42/0.60    inference(superposition,[],[f589,f544])).
% 1.42/0.60  fof(f544,plain,(
% 1.42/0.60    k2_relat_1(sK4) = k11_relat_1(sK4,sK1) | ~spl8_23),
% 1.42/0.60    inference(resolution,[],[f474,f115])).
% 1.42/0.60  fof(f115,plain,(
% 1.42/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.42/0.60    inference(definition_unfolding,[],[f70,f113])).
% 1.42/0.60  fof(f113,plain,(
% 1.42/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.42/0.60    inference(definition_unfolding,[],[f74,f112])).
% 1.42/0.60  fof(f112,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.42/0.60    inference(definition_unfolding,[],[f78,f101])).
% 1.42/0.60  fof(f101,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f6])).
% 1.42/0.60  fof(f6,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.60  fof(f78,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f5])).
% 1.42/0.60  fof(f5,axiom,(
% 1.42/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.60  fof(f74,plain,(
% 1.42/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f4])).
% 1.42/0.60  fof(f4,axiom,(
% 1.42/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.60  fof(f70,plain,(
% 1.42/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.42/0.60    inference(cnf_transformation,[],[f49])).
% 1.42/0.60  fof(f49,plain,(
% 1.42/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 1.42/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f48])).
% 1.42/0.60  fof(f48,plain,(
% 1.42/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 1.42/0.60    introduced(choice_axiom,[])).
% 1.42/0.60  fof(f27,plain,(
% 1.42/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.42/0.60    inference(flattening,[],[f26])).
% 1.42/0.60  fof(f26,plain,(
% 1.42/0.60    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.42/0.60    inference(ennf_transformation,[],[f25])).
% 1.42/0.60  fof(f25,negated_conjecture,(
% 1.42/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.42/0.60    inference(negated_conjecture,[],[f24])).
% 1.42/0.60  fof(f24,conjecture,(
% 1.42/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.42/0.60  fof(f474,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) | k2_relat_1(sK4) = k11_relat_1(sK4,X0)) ) | ~spl8_23),
% 1.42/0.60    inference(resolution,[],[f464,f102])).
% 1.42/0.60  fof(f102,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f39])).
% 1.42/0.60  fof(f39,plain,(
% 1.42/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(ennf_transformation,[],[f20])).
% 1.42/0.60  fof(f20,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.42/0.60  fof(f464,plain,(
% 1.42/0.60    ( ! [X1] : (~v4_relat_1(sK4,k2_enumset1(X1,X1,X1,X1)) | k2_relat_1(sK4) = k11_relat_1(sK4,X1)) ) | ~spl8_23),
% 1.42/0.60    inference(avatar_component_clause,[],[f463])).
% 1.42/0.60  fof(f589,plain,(
% 1.42/0.60    ( ! [X6,X4,X5] : (m1_subset_1(k11_relat_1(sK4,X4),k1_zfmisc_1(X5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))) ) | ~spl8_18),
% 1.42/0.60    inference(superposition,[],[f377,f456])).
% 1.42/0.60  fof(f456,plain,(
% 1.42/0.60    ( ! [X0] : (k11_relat_1(sK4,X0) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0))) ) | ~spl8_18),
% 1.42/0.60    inference(resolution,[],[f408,f117])).
% 1.42/0.60  fof(f117,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.42/0.60    inference(definition_unfolding,[],[f75,f113])).
% 1.42/0.60  fof(f75,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f28])).
% 1.42/0.60  fof(f28,plain,(
% 1.42/0.60    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.42/0.60    inference(ennf_transformation,[],[f12])).
% 1.42/0.60  fof(f12,axiom,(
% 1.42/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.42/0.60  fof(f408,plain,(
% 1.42/0.60    v1_relat_1(sK4) | ~spl8_18),
% 1.42/0.60    inference(avatar_component_clause,[],[f407])).
% 1.42/0.60  fof(f377,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f376])).
% 1.42/0.60  fof(f376,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.60    inference(superposition,[],[f110,f111])).
% 1.42/0.60  fof(f111,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f45])).
% 1.42/0.60  fof(f45,plain,(
% 1.42/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(ennf_transformation,[],[f22])).
% 1.42/0.60  fof(f22,axiom,(
% 1.42/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.42/0.60  fof(f110,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f44])).
% 1.42/0.60  fof(f44,plain,(
% 1.42/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(ennf_transformation,[],[f21])).
% 1.42/0.60  fof(f21,axiom,(
% 1.42/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.42/0.60  fof(f659,plain,(
% 1.42/0.60    spl8_17 | ~spl8_28),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f656])).
% 1.42/0.60  fof(f656,plain,(
% 1.42/0.60    $false | (spl8_17 | ~spl8_28)),
% 1.42/0.60    inference(resolution,[],[f502,f441])).
% 1.42/0.60  fof(f441,plain,(
% 1.42/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | spl8_17),
% 1.42/0.60    inference(superposition,[],[f416,f128])).
% 1.42/0.60  fof(f128,plain,(
% 1.42/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.42/0.60    inference(equality_resolution,[],[f99])).
% 1.42/0.60  fof(f99,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.42/0.60    inference(cnf_transformation,[],[f63])).
% 1.42/0.60  fof(f416,plain,(
% 1.42/0.60    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) ) | spl8_17),
% 1.42/0.60    inference(resolution,[],[f405,f102])).
% 1.42/0.60  fof(f405,plain,(
% 1.42/0.60    ~v4_relat_1(sK4,sK3) | spl8_17),
% 1.42/0.60    inference(avatar_component_clause,[],[f403])).
% 1.42/0.60  fof(f403,plain,(
% 1.42/0.60    spl8_17 <=> v4_relat_1(sK4,sK3)),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.42/0.60  fof(f651,plain,(
% 1.42/0.60    spl8_16 | ~spl8_18 | ~spl8_23 | ~spl8_27 | ~spl8_29),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f649])).
% 1.42/0.60  fof(f649,plain,(
% 1.42/0.60    $false | (spl8_16 | ~spl8_18 | ~spl8_23 | ~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(resolution,[],[f644,f408])).
% 1.42/0.60  fof(f644,plain,(
% 1.42/0.60    ~v1_relat_1(sK4) | (spl8_16 | ~spl8_18 | ~spl8_23 | ~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(resolution,[],[f629,f79])).
% 1.42/0.60  fof(f79,plain,(
% 1.42/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f30])).
% 1.42/0.60  fof(f30,plain,(
% 1.42/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f15])).
% 1.42/0.60  fof(f15,axiom,(
% 1.42/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.42/0.60  fof(f629,plain,(
% 1.42/0.60    ~r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | (spl8_16 | ~spl8_18 | ~spl8_23 | ~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(backward_demodulation,[],[f390,f625])).
% 1.42/0.60  fof(f625,plain,(
% 1.42/0.60    k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) | (~spl8_18 | ~spl8_23 | ~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(forward_demodulation,[],[f621,f544])).
% 1.42/0.60  fof(f621,plain,(
% 1.42/0.60    k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) | (~spl8_18 | ~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(backward_demodulation,[],[f534,f612])).
% 1.42/0.60  fof(f612,plain,(
% 1.42/0.60    sK1 = sK7(k1_relat_1(sK4),k1_xboole_0,sK4) | (~spl8_18 | ~spl8_27)),
% 1.42/0.60    inference(resolution,[],[f609,f497])).
% 1.42/0.60  fof(f497,plain,(
% 1.42/0.60    r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4)) | ~spl8_27),
% 1.42/0.60    inference(avatar_component_clause,[],[f495])).
% 1.42/0.60  fof(f495,plain,(
% 1.42/0.60    spl8_27 <=> r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.42/0.60  fof(f609,plain,(
% 1.42/0.60    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK4)) | sK1 = X7) ) | ~spl8_18),
% 1.42/0.60    inference(resolution,[],[f197,f558])).
% 1.42/0.60  fof(f558,plain,(
% 1.42/0.60    r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl8_18),
% 1.42/0.60    inference(resolution,[],[f557,f115])).
% 1.42/0.60  fof(f557,plain,(
% 1.42/0.60    ( ! [X10,X11] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | r1_tarski(k1_relat_1(sK4),X10)) ) | ~spl8_18),
% 1.42/0.60    inference(resolution,[],[f167,f408])).
% 1.42/0.60  fof(f167,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.42/0.60    inference(resolution,[],[f102,f81])).
% 1.42/0.60  fof(f81,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f50])).
% 1.42/0.60  fof(f50,plain,(
% 1.42/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(nnf_transformation,[],[f32])).
% 1.42/0.60  fof(f32,plain,(
% 1.42/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f13])).
% 1.42/0.60  fof(f13,axiom,(
% 1.42/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.42/0.60  fof(f197,plain,(
% 1.42/0.60    ( ! [X2,X3,X1] : (~r1_tarski(X3,k2_enumset1(X1,X1,X1,X1)) | ~r2_hidden(X2,X3) | X1 = X2) )),
% 1.42/0.60    inference(resolution,[],[f127,f88])).
% 1.42/0.60  fof(f88,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f56])).
% 1.42/0.60  fof(f127,plain,(
% 1.42/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.42/0.60    inference(equality_resolution,[],[f122])).
% 1.42/0.60  fof(f122,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.42/0.60    inference(definition_unfolding,[],[f91,f113])).
% 1.42/0.60  fof(f91,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.42/0.60    inference(cnf_transformation,[],[f60])).
% 1.42/0.60  fof(f60,plain,(
% 1.42/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.42/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 1.42/0.60  fof(f59,plain,(
% 1.42/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.42/0.60    introduced(choice_axiom,[])).
% 1.42/0.60  fof(f58,plain,(
% 1.42/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.42/0.60    inference(rectify,[],[f57])).
% 1.42/0.60  fof(f57,plain,(
% 1.42/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.42/0.60    inference(nnf_transformation,[],[f3])).
% 1.42/0.60  fof(f3,axiom,(
% 1.42/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.42/0.60  fof(f534,plain,(
% 1.42/0.60    k11_relat_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)) = k2_enumset1(k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4)),k1_funct_1(sK4,sK7(k1_relat_1(sK4),k1_xboole_0,sK4))) | (~spl8_27 | ~spl8_29)),
% 1.42/0.60    inference(resolution,[],[f520,f497])).
% 1.42/0.60  fof(f520,plain,(
% 1.42/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0))) ) | ~spl8_29),
% 1.42/0.60    inference(avatar_component_clause,[],[f519])).
% 1.42/0.60  fof(f519,plain,(
% 1.42/0.60    spl8_29 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.42/0.60  fof(f390,plain,(
% 1.42/0.60    ~r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) | spl8_16),
% 1.42/0.60    inference(avatar_component_clause,[],[f388])).
% 1.42/0.60  fof(f388,plain,(
% 1.42/0.60    spl8_16 <=> r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.42/0.60  fof(f521,plain,(
% 1.42/0.60    ~spl8_18 | spl8_29),
% 1.42/0.60    inference(avatar_split_clause,[],[f516,f519,f407])).
% 1.42/0.60  fof(f516,plain,(
% 1.42/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k11_relat_1(sK4,X0) = k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) | ~v1_relat_1(sK4)) )),
% 1.42/0.60    inference(resolution,[],[f118,f68])).
% 1.42/0.60  fof(f68,plain,(
% 1.42/0.60    v1_funct_1(sK4)),
% 1.42/0.60    inference(cnf_transformation,[],[f49])).
% 1.42/0.60  fof(f118,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(definition_unfolding,[],[f83,f113])).
% 1.42/0.60  fof(f83,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f34])).
% 1.42/0.60  fof(f34,plain,(
% 1.42/0.60    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(flattening,[],[f33])).
% 1.42/0.60  fof(f33,plain,(
% 1.42/0.60    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.42/0.60    inference(ennf_transformation,[],[f18])).
% 1.42/0.60  fof(f18,axiom,(
% 1.42/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.42/0.60  fof(f503,plain,(
% 1.42/0.60    spl8_27 | spl8_28 | ~spl8_26),
% 1.42/0.60    inference(avatar_split_clause,[],[f492,f483,f500,f495])).
% 1.42/0.60  fof(f483,plain,(
% 1.42/0.60    spl8_26 <=> ! [X0] : (r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) | sP0(X0,k1_relat_1(sK4),sK4))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.42/0.60  fof(f492,plain,(
% 1.42/0.60    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK7(k1_relat_1(sK4),k1_xboole_0,sK4),k1_relat_1(sK4)) | ~spl8_26),
% 1.42/0.60    inference(superposition,[],[f486,f128])).
% 1.42/0.60  fof(f486,plain,(
% 1.42/0.60    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) | r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))) ) | ~spl8_26),
% 1.42/0.60    inference(resolution,[],[f484,f106])).
% 1.42/0.60  fof(f106,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f65])).
% 1.42/0.60  fof(f65,plain,(
% 1.42/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP0(X0,X1,X2))),
% 1.42/0.60    inference(rectify,[],[f64])).
% 1.42/0.60  fof(f64,plain,(
% 1.42/0.60    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.42/0.60    inference(nnf_transformation,[],[f46])).
% 1.42/0.60  fof(f46,plain,(
% 1.42/0.60    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.42/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.60  fof(f484,plain,(
% 1.42/0.60    ( ! [X0] : (sP0(X0,k1_relat_1(sK4),sK4) | r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))) ) | ~spl8_26),
% 1.42/0.60    inference(avatar_component_clause,[],[f483])).
% 1.42/0.60  fof(f485,plain,(
% 1.42/0.60    ~spl8_18 | spl8_26),
% 1.42/0.60    inference(avatar_split_clause,[],[f480,f483,f407])).
% 1.42/0.60  fof(f480,plain,(
% 1.42/0.60    ( ! [X0] : (r2_hidden(sK7(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) | sP0(X0,k1_relat_1(sK4),sK4) | ~v1_relat_1(sK4)) )),
% 1.42/0.60    inference(resolution,[],[f131,f68])).
% 1.42/0.60  fof(f131,plain,(
% 1.42/0.60    ( ! [X2,X1] : (~v1_funct_1(X2) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP0(X1,k1_relat_1(X2),X2) | ~v1_relat_1(X2)) )),
% 1.42/0.60    inference(equality_resolution,[],[f107])).
% 1.42/0.60  fof(f107,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | r2_hidden(sK7(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f67])).
% 1.42/0.60  fof(f67,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (sP0(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.42/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f66])).
% 1.42/0.60  fof(f66,plain,(
% 1.42/0.60    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 1.42/0.60    introduced(choice_axiom,[])).
% 1.42/0.60  fof(f47,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (sP0(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.42/0.60    inference(definition_folding,[],[f41,f46])).
% 1.42/0.60  fof(f41,plain,(
% 1.42/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.42/0.60    inference(flattening,[],[f40])).
% 1.42/0.60  fof(f40,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.42/0.60    inference(ennf_transformation,[],[f23])).
% 1.42/0.60  fof(f23,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 1.42/0.60  fof(f466,plain,(
% 1.42/0.60    ~spl8_18 | spl8_23 | ~spl8_18),
% 1.42/0.60    inference(avatar_split_clause,[],[f460,f407,f463,f407])).
% 1.42/0.60  fof(f460,plain,(
% 1.42/0.60    ( ! [X0] : (k2_relat_1(sK4) = k11_relat_1(sK4,X0) | ~v1_relat_1(sK4) | ~v4_relat_1(sK4,k2_enumset1(X0,X0,X0,X0))) ) | ~spl8_18),
% 1.42/0.60    inference(superposition,[],[f184,f456])).
% 1.42/0.60  fof(f184,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f183])).
% 1.42/0.60  fof(f183,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.42/0.60    inference(superposition,[],[f80,f84])).
% 1.42/0.60  fof(f84,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f36])).
% 1.42/0.60  fof(f36,plain,(
% 1.42/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(flattening,[],[f35])).
% 1.42/0.60  fof(f35,plain,(
% 1.42/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.42/0.60    inference(ennf_transformation,[],[f17])).
% 1.42/0.60  fof(f17,axiom,(
% 1.42/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.42/0.60  fof(f80,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f31])).
% 1.42/0.60  fof(f31,plain,(
% 1.42/0.60    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f16])).
% 1.42/0.60  fof(f16,axiom,(
% 1.42/0.60    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.42/0.60  fof(f447,plain,(
% 1.42/0.60    spl8_18),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f445])).
% 1.42/0.60  fof(f445,plain,(
% 1.42/0.60    $false | spl8_18),
% 1.42/0.60    inference(resolution,[],[f418,f77])).
% 1.42/0.60  fof(f77,plain,(
% 1.42/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(cnf_transformation,[],[f14])).
% 1.42/0.60  fof(f14,axiom,(
% 1.42/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.42/0.60  fof(f418,plain,(
% 1.42/0.60    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | spl8_18),
% 1.42/0.60    inference(resolution,[],[f415,f115])).
% 1.42/0.60  fof(f415,plain,(
% 1.42/0.60    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_18),
% 1.42/0.60    inference(resolution,[],[f409,f76])).
% 1.42/0.60  fof(f76,plain,(
% 1.42/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f29])).
% 1.42/0.60  fof(f29,plain,(
% 1.42/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.42/0.60    inference(ennf_transformation,[],[f11])).
% 1.42/0.60  fof(f11,axiom,(
% 1.42/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.42/0.60  fof(f409,plain,(
% 1.42/0.60    ~v1_relat_1(sK4) | spl8_18),
% 1.42/0.60    inference(avatar_component_clause,[],[f407])).
% 1.42/0.60  fof(f414,plain,(
% 1.42/0.60    ~spl8_17 | ~spl8_18 | ~spl8_19 | spl8_16),
% 1.42/0.60    inference(avatar_split_clause,[],[f401,f388,f411,f407,f403])).
% 1.42/0.60  fof(f401,plain,(
% 1.42/0.60    ~r1_tarski(k2_relat_1(sK4),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) | ~v1_relat_1(sK4) | ~v4_relat_1(sK4,sK3) | spl8_16),
% 1.42/0.60    inference(superposition,[],[f390,f184])).
% 1.42/0.60  fof(f394,plain,(
% 1.42/0.60    spl8_14),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f392])).
% 1.42/0.60  fof(f392,plain,(
% 1.42/0.60    $false | spl8_14),
% 1.42/0.60    inference(resolution,[],[f381,f115])).
% 1.42/0.60  fof(f381,plain,(
% 1.42/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | spl8_14),
% 1.42/0.60    inference(avatar_component_clause,[],[f379])).
% 1.42/0.60  fof(f379,plain,(
% 1.42/0.60    spl8_14 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.42/0.60  fof(f391,plain,(
% 1.42/0.60    ~spl8_14 | ~spl8_16),
% 1.42/0.60    inference(avatar_split_clause,[],[f375,f388,f379])).
% 1.42/0.60  fof(f375,plain,(
% 1.42/0.60    ~r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.42/0.60    inference(superposition,[],[f114,f111])).
% 1.42/0.60  fof(f114,plain,(
% 1.42/0.60    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 1.42/0.60    inference(definition_unfolding,[],[f72,f113,f113])).
% 1.42/0.60  fof(f72,plain,(
% 1.42/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 1.42/0.60    inference(cnf_transformation,[],[f49])).
% 1.42/0.60  % SZS output end Proof for theBenchmark
% 1.42/0.60  % (10795)------------------------------
% 1.42/0.60  % (10795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.60  % (10795)Termination reason: Refutation
% 1.42/0.60  
% 1.42/0.60  % (10795)Memory used [KB]: 6652
% 1.42/0.60  % (10795)Time elapsed: 0.156 s
% 1.42/0.60  % (10795)------------------------------
% 1.42/0.60  % (10795)------------------------------
% 1.42/0.60  % (10781)Success in time 0.238 s
%------------------------------------------------------------------------------
