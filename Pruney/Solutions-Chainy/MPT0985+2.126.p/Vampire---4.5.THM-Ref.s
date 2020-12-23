%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:19 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 698 expanded)
%              Number of leaves         :   40 ( 213 expanded)
%              Depth                    :   19
%              Number of atoms          :  771 (2504 expanded)
%              Number of equality atoms :  122 ( 373 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f132,f134,f152,f164,f236,f239,f254,f263,f281,f325,f328,f532,f653,f1103,f1272,f1306,f1309,f1574,f1597,f1603])).

fof(f1603,plain,
    ( spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f1598])).

fof(f1598,plain,
    ( $false
    | spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(resolution,[],[f1596,f1504])).

fof(f1504,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f1503,f683])).

fof(f683,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(resolution,[],[f611,f207])).

fof(f207,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f172,f147])).

fof(f147,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(resolution,[],[f144,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f144,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f143,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f74,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
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

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f172,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK4(X3),X4)
      | ~ r1_tarski(X3,X4)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f73,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f138,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f81,f60])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f611,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f610,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f610,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK2,k1_xboole_0))
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f572,f61])).

% (31186)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f572,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)))
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f335,f541])).

fof(f541,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_23 ),
    inference(resolution,[],[f509,f207])).

fof(f509,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl6_23
  <=> ! [X0] : r1_tarski(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f335,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f284,f323])).

fof(f323,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl6_17
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f284,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f256,f280])).

fof(f280,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl6_15
  <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f256,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f240,f253])).

fof(f253,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_13
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f240,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))
    | ~ spl6_11 ),
    inference(resolution,[],[f230,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f230,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_11
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1503,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f1107,f541])).

fof(f1107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f107,f1094])).

fof(f1094,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1092,plain,
    ( spl6_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1596,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f1595,plain,
    ( spl6_37
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1597,plain,
    ( spl6_37
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f1593,f118,f1595])).

fof(f118,plain,
    ( spl6_5
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1593,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f1592])).

fof(f1592,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f1028,f61])).

fof(f1028,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X0,k1_xboole_0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1027])).

% (31165)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f1027,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X0)
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f1026,f94])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1026,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f349,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

% (31192)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ sP0(k1_xboole_0,X1,X0)
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f348,f94])).

fof(f348,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f95,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f1574,plain,
    ( ~ spl6_26
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f1571])).

fof(f1571,plain,
    ( $false
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(resolution,[],[f1562,f147])).

fof(f1562,plain,
    ( ! [X0] : r2_hidden(sK4(k1_xboole_0),X0)
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(resolution,[],[f1186,f144])).

fof(f1186,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | r2_hidden(sK4(k1_xboole_0),X1) )
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f1185,f93])).

fof(f1185,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),X1)
        | ~ r1_tarski(k1_xboole_0,X1) )
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f1184,f1094])).

fof(f1184,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1) )
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f1131,f93])).

fof(f1131,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),X1)
        | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1) )
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f531,f1094])).

fof(f531,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1)
        | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl6_26
  <=> ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1)
        | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1309,plain,
    ( ~ spl6_16
    | spl6_33
    | spl6_34 ),
    inference(avatar_split_clause,[],[f1251,f1092,f1088,f317])).

fof(f317,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1088,plain,
    ( spl6_33
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1251,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f55,f415])).

fof(f415,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f86,f90])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1306,plain,
    ( spl6_3
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f1304])).

fof(f1304,plain,
    ( $false
    | spl6_3
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(resolution,[],[f111,f1235])).

fof(f1235,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f334,f1101])).

fof(f1101,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f1099])).

fof(f1099,plain,
    ( spl6_35
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f334,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f283,f323])).

fof(f283,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f257,f280])).

fof(f257,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f235,f253])).

fof(f235,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl6_12
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1272,plain,
    ( spl6_2
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f1270])).

fof(f1270,plain,
    ( $false
    | spl6_2
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(resolution,[],[f1234,f107])).

fof(f1234,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f333,f1101])).

fof(f333,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f282,f323])).

fof(f282,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f262,f280])).

fof(f262,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl6_14
  <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1103,plain,
    ( ~ spl6_16
    | spl6_35
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f1097,f1088,f1099,f317])).

fof(f1097,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_33 ),
    inference(superposition,[],[f84,f1090])).

fof(f1090,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f653,plain,
    ( spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f651])).

% (31168)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f651,plain,
    ( $false
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(resolution,[],[f617,f60])).

fof(f617,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f616,f93])).

fof(f616,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0))
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f575,f61])).

fof(f575,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)))
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f356,f541])).

fof(f356,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(resolution,[],[f337,f71])).

fof(f337,plain,
    ( r2_hidden(sK4(k2_funct_1(sK3)),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f307,f323])).

fof(f307,plain,
    ( r2_hidden(sK4(k2_funct_1(sK3)),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))
    | spl6_3
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(resolution,[],[f305,f284])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_funct_1(sK3),X0)
        | r2_hidden(sK4(k2_funct_1(sK3)),X0) )
    | spl6_3 ),
    inference(resolution,[],[f201,f111])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X2))
      | r2_hidden(sK4(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f171,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(sK4(X0),X1) ) ),
    inference(resolution,[],[f73,f145])).

fof(f145,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(X1),X1)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f143,f72])).

fof(f532,plain,
    ( spl6_26
    | spl6_23
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f528,f321,f125,f508,f530])).

fof(f125,plain,
    ( spl6_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f528,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK3,X0)
        | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1)
        | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1) )
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(resolution,[],[f500,f171])).

fof(f500,plain,
    ( ! [X15] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X15)
        | r1_tarski(sK3,X15) )
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(resolution,[],[f491,f329])).

fof(f329,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2))
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f167,f323])).

fof(f167,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl6_6 ),
    inference(resolution,[],[f63,f126])).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f491,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f271,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f271,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(sK5(X2,X4),X5)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X5) ) ),
    inference(resolution,[],[f173,f73])).

fof(f173,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK5(X5,X6),X7)
      | ~ r1_tarski(X5,X7)
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f73,f74])).

fof(f328,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f319,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f317])).

fof(f325,plain,
    ( ~ spl6_16
    | spl6_17 ),
    inference(avatar_split_clause,[],[f315,f321,f317])).

fof(f315,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f281,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_15 ),
    inference(avatar_split_clause,[],[f276,f278,f129,f125])).

fof(f129,plain,
    ( spl6_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f276,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f263,plain,
    ( ~ spl6_11
    | ~ spl6_1
    | spl6_14
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f258,f251,f260,f101,f229])).

fof(f101,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f258,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_13 ),
    inference(superposition,[],[f65,f253])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f254,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_13 ),
    inference(avatar_split_clause,[],[f249,f251,f129,f125])).

fof(f249,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f57])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f239,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_11 ),
    inference(avatar_split_clause,[],[f237,f229,f129,f125])).

fof(f237,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_11 ),
    inference(resolution,[],[f231,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f231,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f229])).

fof(f236,plain,
    ( ~ spl6_11
    | spl6_12
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f227,f101,f233,f229])).

fof(f227,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f66,f102])).

fof(f102,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f160,f56])).

fof(f160,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_6 ),
    inference(resolution,[],[f83,f127])).

fof(f127,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f152,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f146,f120])).

fof(f120,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f146,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f144,f77])).

% (31187)Refutation not found, incomplete strategy% (31187)------------------------------
% (31187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31187)Termination reason: Refutation not found, incomplete strategy

% (31187)Memory used [KB]: 10874
% (31187)Time elapsed: 0.070 s
% (31187)------------------------------
% (31187)------------------------------
fof(f134,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f131,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f123,f101,f129,f125])).

fof(f123,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f68,f103])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f59,f109,f105,f101])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (31177)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.52  % (31194)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.17/0.52  % (31174)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.53  % (31187)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (31179)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.54  % (31166)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (31167)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (31170)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.54  % (31177)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f1605,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(avatar_sat_refutation,[],[f112,f132,f134,f152,f164,f236,f239,f254,f263,f281,f325,f328,f532,f653,f1103,f1272,f1306,f1309,f1574,f1597,f1603])).
% 1.30/0.54  fof(f1603,plain,(
% 1.30/0.54    spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_34 | ~spl6_37),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f1598])).
% 1.30/0.54  fof(f1598,plain,(
% 1.30/0.54    $false | (spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_34 | ~spl6_37)),
% 1.30/0.54    inference(resolution,[],[f1596,f1504])).
% 1.30/0.54  fof(f1504,plain,(
% 1.30/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_34)),
% 1.30/0.54    inference(forward_demodulation,[],[f1503,f683])).
% 1.30/0.54  fof(f683,plain,(
% 1.30/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(resolution,[],[f611,f207])).
% 1.30/0.54  fof(f207,plain,(
% 1.30/0.54    ( ! [X5] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X5) )),
% 1.30/0.54    inference(resolution,[],[f172,f147])).
% 1.30/0.54  fof(f147,plain,(
% 1.30/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.30/0.54    inference(resolution,[],[f144,f82])).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.30/0.54  fof(f144,plain,(
% 1.30/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.54    inference(resolution,[],[f143,f60])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    v1_xboole_0(k1_xboole_0)),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    v1_xboole_0(k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.54  fof(f143,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(resolution,[],[f74,f71])).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f43])).
% 1.30/0.54  fof(f43,plain,(
% 1.30/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.54    inference(rectify,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.54    inference(nnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f44])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.54    inference(nnf_transformation,[],[f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.54  fof(f172,plain,(
% 1.30/0.54    ( ! [X4,X3] : (r2_hidden(sK4(X3),X4) | ~r1_tarski(X3,X4) | k1_xboole_0 = X3) )),
% 1.30/0.54    inference(resolution,[],[f73,f141])).
% 1.30/0.54  fof(f141,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.30/0.54    inference(resolution,[],[f138,f72])).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f43])).
% 1.30/0.54  fof(f138,plain,(
% 1.30/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.30/0.54    inference(resolution,[],[f81,f60])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.30/0.54  fof(f73,plain,(
% 1.30/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f611,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(forward_demodulation,[],[f610,f93])).
% 1.30/0.54  fof(f93,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f80])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f50])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.30/0.54    inference(flattening,[],[f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.30/0.54    inference(nnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.30/0.54  fof(f610,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK2,k1_xboole_0)) | (~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(forward_demodulation,[],[f572,f61])).
% 1.30/0.54  % (31186)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.30/0.54  fof(f572,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0))) | (~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(backward_demodulation,[],[f335,f541])).
% 1.30/0.54  fof(f541,plain,(
% 1.30/0.54    k1_xboole_0 = sK3 | ~spl6_23),
% 1.30/0.54    inference(resolution,[],[f509,f207])).
% 1.30/0.54  fof(f509,plain,(
% 1.30/0.54    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_23),
% 1.30/0.54    inference(avatar_component_clause,[],[f508])).
% 1.30/0.54  fof(f508,plain,(
% 1.30/0.54    spl6_23 <=> ! [X0] : r1_tarski(sK3,X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.30/0.54  fof(f335,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | (~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17)),
% 1.30/0.54    inference(backward_demodulation,[],[f284,f323])).
% 1.30/0.54  fof(f323,plain,(
% 1.30/0.54    sK2 = k2_relat_1(sK3) | ~spl6_17),
% 1.30/0.54    inference(avatar_component_clause,[],[f321])).
% 1.30/0.54  fof(f321,plain,(
% 1.30/0.54    spl6_17 <=> sK2 = k2_relat_1(sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.30/0.54  fof(f284,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) | (~spl6_11 | ~spl6_13 | ~spl6_15)),
% 1.30/0.54    inference(backward_demodulation,[],[f256,f280])).
% 1.30/0.54  fof(f280,plain,(
% 1.30/0.54    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~spl6_15),
% 1.30/0.54    inference(avatar_component_clause,[],[f278])).
% 1.30/0.54  fof(f278,plain,(
% 1.30/0.54    spl6_15 <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.30/0.54  fof(f256,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))) | (~spl6_11 | ~spl6_13)),
% 1.30/0.54    inference(backward_demodulation,[],[f240,f253])).
% 1.30/0.54  fof(f253,plain,(
% 1.30/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl6_13),
% 1.30/0.54    inference(avatar_component_clause,[],[f251])).
% 1.30/0.54  fof(f251,plain,(
% 1.30/0.54    spl6_13 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.30/0.54  fof(f240,plain,(
% 1.30/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))) | ~spl6_11),
% 1.30/0.54    inference(resolution,[],[f230,f63])).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.30/0.54  fof(f230,plain,(
% 1.30/0.54    v1_relat_1(k2_funct_1(sK3)) | ~spl6_11),
% 1.30/0.54    inference(avatar_component_clause,[],[f229])).
% 1.30/0.54  fof(f229,plain,(
% 1.30/0.54    spl6_11 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.30/0.54  fof(f1503,plain,(
% 1.30/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | (spl6_2 | ~spl6_23 | ~spl6_34)),
% 1.30/0.54    inference(forward_demodulation,[],[f1107,f541])).
% 1.30/0.54  fof(f1107,plain,(
% 1.30/0.54    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | (spl6_2 | ~spl6_34)),
% 1.30/0.54    inference(backward_demodulation,[],[f107,f1094])).
% 1.30/0.54  fof(f1094,plain,(
% 1.30/0.54    k1_xboole_0 = sK2 | ~spl6_34),
% 1.30/0.54    inference(avatar_component_clause,[],[f1092])).
% 1.30/0.54  fof(f1092,plain,(
% 1.30/0.54    spl6_34 <=> k1_xboole_0 = sK2),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.30/0.54  fof(f107,plain,(
% 1.30/0.54    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | spl6_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f105])).
% 1.30/0.54  fof(f105,plain,(
% 1.30/0.54    spl6_2 <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.30/0.54  fof(f1596,plain,(
% 1.30/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl6_37),
% 1.30/0.54    inference(avatar_component_clause,[],[f1595])).
% 1.30/0.54  fof(f1595,plain,(
% 1.30/0.54    spl6_37 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.30/0.54  fof(f1597,plain,(
% 1.30/0.54    spl6_37 | ~spl6_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f1593,f118,f1595])).
% 1.30/0.54  fof(f118,plain,(
% 1.30/0.54    spl6_5 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.30/0.54  fof(f1593,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f1592])).
% 1.30/0.54  fof(f1592,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.30/0.54    inference(superposition,[],[f1028,f61])).
% 1.30/0.54  fof(f1028,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X0,k1_xboole_0,X1)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f1027])).
% 1.30/0.54  % (31165)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  fof(f1027,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X0) | v1_funct_2(X0,k1_xboole_0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.30/0.54    inference(forward_demodulation,[],[f1026,f94])).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.30/0.54    inference(equality_resolution,[],[f79])).
% 1.30/0.54  fof(f79,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f50])).
% 1.30/0.54  fof(f1026,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X0) | v1_funct_2(X0,k1_xboole_0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.30/0.54    inference(resolution,[],[f349,f90])).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(nnf_transformation,[],[f37])).
% 1.30/0.54  % (31192)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(definition_folding,[],[f35,f36])).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(flattening,[],[f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(ennf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.30/0.54  fof(f349,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~sP0(k1_xboole_0,X1,X0) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 1.30/0.54    inference(forward_demodulation,[],[f348,f94])).
% 1.30/0.54  fof(f348,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~sP0(k1_xboole_0,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 1.30/0.54    inference(superposition,[],[f95,f84])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.30/0.54  fof(f95,plain,(
% 1.30/0.54    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 1.30/0.54    inference(equality_resolution,[],[f89])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f52])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.30/0.54    inference(rectify,[],[f51])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.30/0.54    inference(nnf_transformation,[],[f36])).
% 1.30/0.54  fof(f1574,plain,(
% 1.30/0.54    ~spl6_26 | ~spl6_34),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f1571])).
% 1.30/0.54  fof(f1571,plain,(
% 1.30/0.54    $false | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(resolution,[],[f1562,f147])).
% 1.30/0.54  fof(f1562,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0),X0)) ) | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(resolution,[],[f1186,f144])).
% 1.30/0.54  fof(f1186,plain,(
% 1.30/0.54    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(sK4(k1_xboole_0),X1)) ) | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(forward_demodulation,[],[f1185,f93])).
% 1.30/0.54  fof(f1185,plain,(
% 1.30/0.54    ( ! [X1] : (r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),X1) | ~r1_tarski(k1_xboole_0,X1)) ) | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(forward_demodulation,[],[f1184,f1094])).
% 1.30/0.54  fof(f1184,plain,(
% 1.30/0.54    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1)) ) | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(forward_demodulation,[],[f1131,f93])).
% 1.30/0.54  fof(f1131,plain,(
% 1.30/0.54    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0),X1) | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1)) ) | (~spl6_26 | ~spl6_34)),
% 1.30/0.54    inference(backward_demodulation,[],[f531,f1094])).
% 1.30/0.54  fof(f531,plain,(
% 1.30/0.54    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1) | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1)) ) | ~spl6_26),
% 1.30/0.54    inference(avatar_component_clause,[],[f530])).
% 1.30/0.54  fof(f530,plain,(
% 1.30/0.54    spl6_26 <=> ! [X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1) | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.30/0.54  fof(f1309,plain,(
% 1.30/0.54    ~spl6_16 | spl6_33 | spl6_34),
% 1.30/0.54    inference(avatar_split_clause,[],[f1251,f1092,f1088,f317])).
% 1.30/0.54  fof(f317,plain,(
% 1.30/0.54    spl6_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.30/0.54  fof(f1088,plain,(
% 1.30/0.54    spl6_33 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.30/0.54  fof(f1251,plain,(
% 1.30/0.54    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.30/0.54    inference(resolution,[],[f55,f415])).
% 1.30/0.54  fof(f415,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,X2) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.30/0.54    inference(resolution,[],[f86,f90])).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f52])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    v1_funct_2(sK3,sK1,sK2)),
% 1.30/0.54    inference(cnf_transformation,[],[f39])).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f38])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.30/0.54    inference(flattening,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.30/0.54    inference(ennf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,negated_conjecture,(
% 1.30/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.30/0.54    inference(negated_conjecture,[],[f17])).
% 1.30/0.54  fof(f17,conjecture,(
% 1.30/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.30/0.54  fof(f1306,plain,(
% 1.30/0.54    spl6_3 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_35),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f1304])).
% 1.30/0.54  fof(f1304,plain,(
% 1.30/0.54    $false | (spl6_3 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_35)),
% 1.30/0.54    inference(resolution,[],[f111,f1235])).
% 1.30/0.54  fof(f1235,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_35)),
% 1.30/0.54    inference(backward_demodulation,[],[f334,f1101])).
% 1.30/0.54  fof(f1101,plain,(
% 1.30/0.54    sK1 = k1_relat_1(sK3) | ~spl6_35),
% 1.30/0.54    inference(avatar_component_clause,[],[f1099])).
% 1.30/0.54  fof(f1099,plain,(
% 1.30/0.54    spl6_35 <=> sK1 = k1_relat_1(sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.30/0.54  fof(f334,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | (~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_17)),
% 1.30/0.54    inference(backward_demodulation,[],[f283,f323])).
% 1.30/0.54  fof(f283,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | (~spl6_12 | ~spl6_13 | ~spl6_15)),
% 1.30/0.54    inference(backward_demodulation,[],[f257,f280])).
% 1.30/0.54  fof(f257,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) | (~spl6_12 | ~spl6_13)),
% 1.30/0.54    inference(backward_demodulation,[],[f235,f253])).
% 1.30/0.54  fof(f235,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~spl6_12),
% 1.30/0.54    inference(avatar_component_clause,[],[f233])).
% 1.30/0.54  fof(f233,plain,(
% 1.30/0.54    spl6_12 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.30/0.54  fof(f111,plain,(
% 1.30/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.30/0.54    inference(avatar_component_clause,[],[f109])).
% 1.30/0.54  fof(f109,plain,(
% 1.30/0.54    spl6_3 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.30/0.54  fof(f1272,plain,(
% 1.30/0.54    spl6_2 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_35),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f1270])).
% 1.30/0.54  fof(f1270,plain,(
% 1.30/0.54    $false | (spl6_2 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_35)),
% 1.30/0.54    inference(resolution,[],[f1234,f107])).
% 1.30/0.54  fof(f1234,plain,(
% 1.30/0.54    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | (~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_35)),
% 1.30/0.54    inference(backward_demodulation,[],[f333,f1101])).
% 1.30/0.54  fof(f333,plain,(
% 1.30/0.54    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | (~spl6_14 | ~spl6_15 | ~spl6_17)),
% 1.30/0.54    inference(backward_demodulation,[],[f282,f323])).
% 1.30/0.54  fof(f282,plain,(
% 1.30/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | (~spl6_14 | ~spl6_15)),
% 1.30/0.54    inference(backward_demodulation,[],[f262,f280])).
% 1.30/0.54  fof(f262,plain,(
% 1.30/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~spl6_14),
% 1.30/0.54    inference(avatar_component_clause,[],[f260])).
% 1.30/0.54  fof(f260,plain,(
% 1.30/0.54    spl6_14 <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.30/0.54  fof(f1103,plain,(
% 1.30/0.54    ~spl6_16 | spl6_35 | ~spl6_33),
% 1.30/0.54    inference(avatar_split_clause,[],[f1097,f1088,f1099,f317])).
% 1.30/0.54  fof(f1097,plain,(
% 1.30/0.54    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_33),
% 1.30/0.54    inference(superposition,[],[f84,f1090])).
% 1.30/0.54  fof(f1090,plain,(
% 1.30/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_33),
% 1.30/0.54    inference(avatar_component_clause,[],[f1088])).
% 1.30/0.54  fof(f653,plain,(
% 1.30/0.54    spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f651])).
% 1.30/0.54  % (31168)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  fof(f651,plain,(
% 1.30/0.54    $false | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(resolution,[],[f617,f60])).
% 1.30/0.54  fof(f617,plain,(
% 1.30/0.54    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(forward_demodulation,[],[f616,f93])).
% 1.30/0.54  fof(f616,plain,(
% 1.30/0.54    ~v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(forward_demodulation,[],[f575,f61])).
% 1.30/0.54  fof(f575,plain,(
% 1.30/0.54    ~v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0))) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17 | ~spl6_23)),
% 1.30/0.54    inference(backward_demodulation,[],[f356,f541])).
% 1.30/0.54  fof(f356,plain,(
% 1.30/0.54    ~v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(sK3))) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17)),
% 1.30/0.54    inference(resolution,[],[f337,f71])).
% 1.30/0.54  fof(f337,plain,(
% 1.30/0.54    r2_hidden(sK4(k2_funct_1(sK3)),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_17)),
% 1.30/0.54    inference(backward_demodulation,[],[f307,f323])).
% 1.30/0.54  fof(f307,plain,(
% 1.30/0.54    r2_hidden(sK4(k2_funct_1(sK3)),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) | (spl6_3 | ~spl6_11 | ~spl6_13 | ~spl6_15)),
% 1.30/0.54    inference(resolution,[],[f305,f284])).
% 1.30/0.54  fof(f305,plain,(
% 1.30/0.54    ( ! [X0] : (~r1_tarski(k2_funct_1(sK3),X0) | r2_hidden(sK4(k2_funct_1(sK3)),X0)) ) | spl6_3),
% 1.30/0.54    inference(resolution,[],[f201,f111])).
% 1.30/0.54  fof(f201,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK4(X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(resolution,[],[f171,f77])).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f48])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.30/0.54    inference(nnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.54  fof(f171,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | r2_hidden(sK4(X0),X1)) )),
% 1.30/0.54    inference(resolution,[],[f73,f145])).
% 1.30/0.54  fof(f145,plain,(
% 1.30/0.54    ( ! [X2,X1] : (r2_hidden(sK4(X1),X1) | r1_tarski(X1,X2)) )),
% 1.30/0.54    inference(resolution,[],[f143,f72])).
% 1.30/0.54  fof(f532,plain,(
% 1.30/0.54    spl6_26 | spl6_23 | ~spl6_6 | ~spl6_17),
% 1.30/0.54    inference(avatar_split_clause,[],[f528,f321,f125,f508,f530])).
% 1.30/0.54  fof(f125,plain,(
% 1.30/0.54    spl6_6 <=> v1_relat_1(sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.30/0.54  fof(f528,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(sK3,X0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X1) | r2_hidden(sK4(k2_zfmisc_1(k1_relat_1(sK3),sK2)),X1)) ) | (~spl6_6 | ~spl6_17)),
% 1.30/0.54    inference(resolution,[],[f500,f171])).
% 1.30/0.54  fof(f500,plain,(
% 1.30/0.54    ( ! [X15] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK2),X15) | r1_tarski(sK3,X15)) ) | (~spl6_6 | ~spl6_17)),
% 1.30/0.54    inference(resolution,[],[f491,f329])).
% 1.30/0.54  fof(f329,plain,(
% 1.30/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) | (~spl6_6 | ~spl6_17)),
% 1.30/0.54    inference(backward_demodulation,[],[f167,f323])).
% 1.30/0.54  fof(f167,plain,(
% 1.30/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl6_6),
% 1.30/0.54    inference(resolution,[],[f63,f126])).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    v1_relat_1(sK3) | ~spl6_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f125])).
% 1.30/0.54  fof(f491,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X2,X1)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f486])).
% 1.30/0.54  fof(f486,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(resolution,[],[f271,f75])).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f271,plain,(
% 1.30/0.54    ( ! [X4,X2,X5,X3] : (r2_hidden(sK5(X2,X4),X5) | r1_tarski(X2,X4) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X5)) )),
% 1.30/0.54    inference(resolution,[],[f173,f73])).
% 1.30/0.54  fof(f173,plain,(
% 1.30/0.54    ( ! [X6,X7,X5] : (r2_hidden(sK5(X5,X6),X7) | ~r1_tarski(X5,X7) | r1_tarski(X5,X6)) )),
% 1.30/0.54    inference(resolution,[],[f73,f74])).
% 1.30/0.54  fof(f328,plain,(
% 1.30/0.54    spl6_16),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f326])).
% 1.30/0.54  fof(f326,plain,(
% 1.30/0.54    $false | spl6_16),
% 1.30/0.54    inference(resolution,[],[f319,f56])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.30/0.54    inference(cnf_transformation,[],[f39])).
% 1.30/0.54  fof(f319,plain,(
% 1.30/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_16),
% 1.30/0.54    inference(avatar_component_clause,[],[f317])).
% 1.30/0.54  fof(f325,plain,(
% 1.30/0.54    ~spl6_16 | spl6_17),
% 1.30/0.54    inference(avatar_split_clause,[],[f315,f321,f317])).
% 1.30/0.54  fof(f315,plain,(
% 1.30/0.54    sK2 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.30/0.54    inference(superposition,[],[f58,f85])).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(ennf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.30/0.54    inference(cnf_transformation,[],[f39])).
% 1.30/0.54  fof(f281,plain,(
% 1.30/0.54    ~spl6_6 | ~spl6_7 | spl6_15),
% 1.30/0.54    inference(avatar_split_clause,[],[f276,f278,f129,f125])).
% 1.30/0.54  fof(f129,plain,(
% 1.30/0.54    spl6_7 <=> v1_funct_1(sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.30/0.54  fof(f276,plain,(
% 1.30/0.54    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.30/0.54    inference(resolution,[],[f70,f57])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    v2_funct_1(sK3)),
% 1.30/0.54    inference(cnf_transformation,[],[f39])).
% 1.30/0.54  fof(f70,plain,(
% 1.30/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.30/0.54  fof(f263,plain,(
% 1.30/0.54    ~spl6_11 | ~spl6_1 | spl6_14 | ~spl6_13),
% 1.30/0.54    inference(avatar_split_clause,[],[f258,f251,f260,f101,f229])).
% 1.30/0.54  fof(f101,plain,(
% 1.30/0.54    spl6_1 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.30/0.54  fof(f258,plain,(
% 1.30/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_13),
% 1.30/0.54    inference(superposition,[],[f65,f253])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,axiom,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.30/0.54  fof(f254,plain,(
% 1.30/0.54    ~spl6_6 | ~spl6_7 | spl6_13),
% 1.30/0.54    inference(avatar_split_clause,[],[f249,f251,f129,f125])).
% 1.30/0.54  fof(f249,plain,(
% 1.30/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.30/0.54    inference(resolution,[],[f69,f57])).
% 1.30/0.54  fof(f69,plain,(
% 1.30/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f27])).
% 1.30/0.54  fof(f239,plain,(
% 1.30/0.54    ~spl6_6 | ~spl6_7 | spl6_11),
% 1.30/0.54    inference(avatar_split_clause,[],[f237,f229,f129,f125])).
% 1.30/0.54  fof(f237,plain,(
% 1.30/0.54    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_11),
% 1.30/0.54    inference(resolution,[],[f231,f67])).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.30/0.54  fof(f231,plain,(
% 1.30/0.54    ~v1_relat_1(k2_funct_1(sK3)) | spl6_11),
% 1.30/0.54    inference(avatar_component_clause,[],[f229])).
% 1.30/0.54  fof(f236,plain,(
% 1.30/0.54    ~spl6_11 | spl6_12 | ~spl6_1),
% 1.30/0.54    inference(avatar_split_clause,[],[f227,f101,f233,f229])).
% 1.30/0.54  fof(f227,plain,(
% 1.30/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_1),
% 1.30/0.54    inference(resolution,[],[f66,f102])).
% 1.30/0.54  fof(f102,plain,(
% 1.30/0.54    v1_funct_1(k2_funct_1(sK3)) | ~spl6_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f101])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f164,plain,(
% 1.30/0.54    spl6_6),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f161])).
% 1.30/0.54  fof(f161,plain,(
% 1.30/0.54    $false | spl6_6),
% 1.30/0.54    inference(resolution,[],[f160,f56])).
% 1.30/0.54  fof(f160,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_6),
% 1.30/0.54    inference(resolution,[],[f83,f127])).
% 1.30/0.54  fof(f127,plain,(
% 1.30/0.54    ~v1_relat_1(sK3) | spl6_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f125])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.54  fof(f152,plain,(
% 1.30/0.54    spl6_5),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f150])).
% 1.30/0.54  fof(f150,plain,(
% 1.30/0.54    $false | spl6_5),
% 1.30/0.54    inference(resolution,[],[f146,f120])).
% 1.30/0.54  fof(f120,plain,(
% 1.30/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_5),
% 1.30/0.54    inference(avatar_component_clause,[],[f118])).
% 1.30/0.54  fof(f146,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(resolution,[],[f144,f77])).
% 1.30/0.55  % (31187)Refutation not found, incomplete strategy% (31187)------------------------------
% 1.30/0.55  % (31187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (31187)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (31187)Memory used [KB]: 10874
% 1.30/0.55  % (31187)Time elapsed: 0.070 s
% 1.30/0.55  % (31187)------------------------------
% 1.30/0.55  % (31187)------------------------------
% 1.30/0.55  fof(f134,plain,(
% 1.30/0.55    spl6_7),
% 1.30/0.55    inference(avatar_contradiction_clause,[],[f133])).
% 1.30/0.55  fof(f133,plain,(
% 1.30/0.55    $false | spl6_7),
% 1.30/0.55    inference(resolution,[],[f131,f54])).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    v1_funct_1(sK3)),
% 1.30/0.55    inference(cnf_transformation,[],[f39])).
% 1.30/0.55  fof(f131,plain,(
% 1.30/0.55    ~v1_funct_1(sK3) | spl6_7),
% 1.30/0.55    inference(avatar_component_clause,[],[f129])).
% 1.30/0.55  fof(f132,plain,(
% 1.30/0.55    ~spl6_6 | ~spl6_7 | spl6_1),
% 1.30/0.55    inference(avatar_split_clause,[],[f123,f101,f129,f125])).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_1),
% 1.30/0.55    inference(resolution,[],[f68,f103])).
% 1.30/0.55  fof(f103,plain,(
% 1.30/0.55    ~v1_funct_1(k2_funct_1(sK3)) | spl6_1),
% 1.30/0.55    inference(avatar_component_clause,[],[f101])).
% 1.30/0.55  fof(f68,plain,(
% 1.30/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f25])).
% 1.30/0.55  fof(f112,plain,(
% 1.30/0.55    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.30/0.55    inference(avatar_split_clause,[],[f59,f109,f105,f101])).
% 1.30/0.55  fof(f59,plain,(
% 1.30/0.55    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.30/0.55    inference(cnf_transformation,[],[f39])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (31177)------------------------------
% 1.30/0.55  % (31177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (31177)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (31177)Memory used [KB]: 6652
% 1.30/0.55  % (31177)Time elapsed: 0.109 s
% 1.30/0.55  % (31177)------------------------------
% 1.30/0.55  % (31177)------------------------------
% 1.30/0.55  % (31164)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.55  % (31162)Success in time 0.184 s
%------------------------------------------------------------------------------
