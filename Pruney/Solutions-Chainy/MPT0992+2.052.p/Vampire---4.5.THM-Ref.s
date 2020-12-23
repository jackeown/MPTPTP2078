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
% DateTime   : Thu Dec  3 13:03:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 762 expanded)
%              Number of leaves         :   41 ( 216 expanded)
%              Depth                    :   16
%              Number of atoms          :  614 (4335 expanded)
%              Number of equality atoms :  112 ( 961 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f117,f171,f189,f199,f234,f255,f304,f345,f686,f696,f946,f971,f975,f982,f985,f1101,f1280,f1295,f1372,f1381,f1413,f1691])).

fof(f1691,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_24
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f1689])).

fof(f1689,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_24
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f1426,f1675])).

fof(f1675,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_24
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f1429,f1649])).

fof(f1649,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl5_24
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f344,f273])).

fof(f273,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl5_24
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f344,plain,
    ( ! [X0] : sK3 = k7_relat_1(sK3,X0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl5_27
  <=> ! [X0] : sK3 = k7_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1429,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f1399,f273])).

fof(f1399,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f1388,f161])).

fof(f161,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1388,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f1102,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1102,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f106,f141])).

fof(f141,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_subsumption,[],[f53,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1426,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(backward_demodulation,[],[f1391,f273])).

fof(f1391,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f1313,f139])).

fof(f1313,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f54,f116])).

fof(f116,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f1413,plain,
    ( ~ spl5_23
    | spl5_24
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1411,f115,f272,f269])).

fof(f269,plain,
    ( spl5_23
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1411,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f1344,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1344,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1317,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f1317,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f134,f116])).

fof(f134,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f1381,plain,
    ( spl5_9
    | ~ spl5_13
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1379,f115,f167,f144])).

fof(f144,plain,
    ( spl5_9
  <=> ! [X2] : ~ r2_hidden(X2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f167,plain,
    ( spl5_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1379,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f1343,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f1343,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1314,f95])).

fof(f1314,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f55,f116])).

fof(f1372,plain,
    ( ~ spl5_11
    | spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1367,f115,f160,f157])).

fof(f157,plain,
    ( spl5_11
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1367,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f1315,f69])).

fof(f1315,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f56,f116])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1295,plain,
    ( spl5_30
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f531,f147,f366])).

fof(f366,plain,
    ( spl5_30
  <=> ! [X9,X10] : ~ r2_hidden(X9,k7_relat_1(sK3,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f147,plain,
    ( spl5_10
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f531,plain,(
    ! [X10,X9] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X9,k7_relat_1(sK3,X10)) ) ),
    inference(resolution,[],[f329,f88])).

fof(f329,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f53,f55,f328])).

fof(f328,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f91,f141])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1280,plain,
    ( spl5_2
    | ~ spl5_73 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | spl5_2
    | ~ spl5_73 ),
    inference(resolution,[],[f1105,f794])).

fof(f794,plain,(
    ! [X2] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1) ),
    inference(resolution,[],[f788,f73])).

fof(f788,plain,(
    ! [X0] : m1_subset_1(k2_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f329,f787])).

fof(f787,plain,(
    ! [X0] :
      ( m1_subset_1(k2_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f81,f347])).

fof(f347,plain,(
    ! [X1] : k2_relset_1(sK0,sK1,k7_relat_1(sK3,X1)) = k2_relat_1(k7_relat_1(sK3,X1)) ),
    inference(resolution,[],[f329,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f1105,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl5_2
    | ~ spl5_73 ),
    inference(resolution,[],[f1102,f970])).

fof(f970,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) )
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f969])).

fof(f969,plain,
    ( spl5_73
  <=> ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1101,plain,
    ( spl5_3
    | ~ spl5_74 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl5_3
    | ~ spl5_74 ),
    inference(resolution,[],[f1056,f794])).

fof(f1056,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl5_3
    | ~ spl5_74 ),
    inference(resolution,[],[f974,f953])).

% (31584)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f953,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f109,f141])).

fof(f109,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f974,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl5_74
  <=> ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f985,plain,(
    spl5_72 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | spl5_72 ),
    inference(resolution,[],[f967,f327])).

fof(f327,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK3,X1)) ),
    inference(backward_demodulation,[],[f142,f141])).

fof(f142,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(global_subsumption,[],[f53,f132])).

fof(f132,plain,(
    ! [X1] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f967,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl5_72 ),
    inference(avatar_component_clause,[],[f966])).

fof(f966,plain,
    ( spl5_72
  <=> v1_funct_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f982,plain,(
    spl5_71 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | spl5_71 ),
    inference(resolution,[],[f964,f346])).

fof(f346,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f329,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f964,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl5_71 ),
    inference(avatar_component_clause,[],[f963])).

fof(f963,plain,
    ( spl5_71
  <=> v1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f975,plain,
    ( ~ spl5_71
    | ~ spl5_72
    | spl5_74
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f960,f230,f973,f966,f963])).

fof(f230,plain,
    ( spl5_22
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f960,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_22 ),
    inference(superposition,[],[f66,f955])).

fof(f955,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_22 ),
    inference(resolution,[],[f56,f231])).

fof(f231,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f230])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f971,plain,
    ( ~ spl5_71
    | ~ spl5_72
    | spl5_73
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f959,f230,f969,f966,f963])).

fof(f959,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl5_22 ),
    inference(superposition,[],[f65,f955])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

% (31565)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f946,plain,
    ( spl5_3
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | spl5_3
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(resolution,[],[f943,f541])).

fof(f541,plain,
    ( ! [X0,X1] : r1_tarski(k7_relat_1(sK3,X0),X1)
    | ~ spl5_30 ),
    inference(resolution,[],[f367,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f367,plain,
    ( ! [X10,X9] : ~ r2_hidden(X9,k7_relat_1(sK3,X10))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f366])).

fof(f943,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | spl5_3
    | ~ spl5_12 ),
    inference(resolution,[],[f941,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f941,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f940,f141])).

fof(f940,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f939,f95])).

fof(f939,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f109,f161])).

fof(f696,plain,
    ( ~ spl5_18
    | spl5_22
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f693,f137,f230,f216])).

fof(f216,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f137,plain,
    ( spl5_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f693,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl5_8 ),
    inference(superposition,[],[f63,f315])).

fof(f315,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f128,f138])).

fof(f138,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f128,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
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

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f686,plain,
    ( spl5_8
    | spl5_4 ),
    inference(avatar_split_clause,[],[f685,f112,f137])).

fof(f685,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(global_subsumption,[],[f54,f679])).

fof(f679,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f35])).

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

fof(f345,plain,
    ( ~ spl5_18
    | spl5_27
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f339,f144,f343,f216])).

fof(f339,plain,
    ( ! [X0] :
        ( sK3 = k7_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_9 ),
    inference(resolution,[],[f302,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f302,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK3)
        | sK3 = X1 )
    | ~ spl5_9 ),
    inference(resolution,[],[f262,f69])).

fof(f262,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl5_9 ),
    inference(resolution,[],[f145,f71])).

fof(f145,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f304,plain,(
    spl5_23 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl5_23 ),
    inference(resolution,[],[f270,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f270,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f269])).

fof(f255,plain,
    ( ~ spl5_5
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl5_5
    | spl5_10 ),
    inference(subsumption_resolution,[],[f59,f247])).

fof(f247,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_5
    | spl5_10 ),
    inference(forward_demodulation,[],[f243,f95])).

fof(f243,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_5
    | spl5_10 ),
    inference(backward_demodulation,[],[f148,f116])).

fof(f148,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f234,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl5_18 ),
    inference(subsumption_resolution,[],[f126,f217])).

fof(f217,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f216])).

fof(f126,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f78])).

fof(f199,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f103,f142])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f189,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f158,f60])).

fof(f158,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f171,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_13 ),
    inference(subsumption_resolution,[],[f59,f168])).

fof(f168,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f117,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f57,f115,f112])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f108,f105,f102])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (31558)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (31561)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.49  % (31577)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (31579)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (31559)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (31578)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (31580)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (31570)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31571)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (31555)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (31576)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (31586)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (31560)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (31562)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (31564)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (31568)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (31556)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31588)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (31563)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (31582)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (31583)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (31558)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (31573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (31587)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (31572)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.55  % (31566)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (31585)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (31581)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f1692,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(avatar_sat_refutation,[],[f110,f117,f171,f189,f199,f234,f255,f304,f345,f686,f696,f946,f971,f975,f982,f985,f1101,f1280,f1295,f1372,f1381,f1413,f1691])).
% 1.47/0.55  fof(f1691,plain,(
% 1.47/0.55    spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_12 | ~spl5_24 | ~spl5_27),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f1689])).
% 1.47/0.55  fof(f1689,plain,(
% 1.47/0.55    $false | (spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_12 | ~spl5_24 | ~spl5_27)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1426,f1675])).
% 1.47/0.55  fof(f1675,plain,(
% 1.47/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_12 | ~spl5_24 | ~spl5_27)),
% 1.47/0.55    inference(backward_demodulation,[],[f1429,f1649])).
% 1.47/0.55  fof(f1649,plain,(
% 1.47/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl5_24 | ~spl5_27)),
% 1.47/0.55    inference(forward_demodulation,[],[f344,f273])).
% 1.47/0.55  fof(f273,plain,(
% 1.47/0.55    k1_xboole_0 = sK3 | ~spl5_24),
% 1.47/0.55    inference(avatar_component_clause,[],[f272])).
% 1.47/0.55  fof(f272,plain,(
% 1.47/0.55    spl5_24 <=> k1_xboole_0 = sK3),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.47/0.55  fof(f344,plain,(
% 1.47/0.55    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0)) ) | ~spl5_27),
% 1.47/0.55    inference(avatar_component_clause,[],[f343])).
% 1.47/0.55  fof(f343,plain,(
% 1.47/0.55    spl5_27 <=> ! [X0] : sK3 = k7_relat_1(sK3,X0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.47/0.55  fof(f1429,plain,(
% 1.47/0.55    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_12 | ~spl5_24)),
% 1.47/0.55    inference(forward_demodulation,[],[f1399,f273])).
% 1.47/0.55  fof(f1399,plain,(
% 1.47/0.55    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_4 | ~spl5_12)),
% 1.47/0.55    inference(backward_demodulation,[],[f1388,f161])).
% 1.47/0.55  fof(f161,plain,(
% 1.47/0.55    k1_xboole_0 = sK2 | ~spl5_12),
% 1.47/0.55    inference(avatar_component_clause,[],[f160])).
% 1.47/0.55  fof(f160,plain,(
% 1.47/0.55    spl5_12 <=> k1_xboole_0 = sK2),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.47/0.55  fof(f1388,plain,(
% 1.47/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl5_2 | ~spl5_4)),
% 1.47/0.55    inference(backward_demodulation,[],[f1102,f139])).
% 1.47/0.55  fof(f139,plain,(
% 1.47/0.55    k1_xboole_0 = sK1 | ~spl5_4),
% 1.47/0.55    inference(avatar_component_clause,[],[f112])).
% 1.47/0.55  fof(f112,plain,(
% 1.47/0.55    spl5_4 <=> k1_xboole_0 = sK1),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.47/0.55  fof(f1102,plain,(
% 1.47/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl5_2),
% 1.47/0.55    inference(forward_demodulation,[],[f106,f141])).
% 1.47/0.55  fof(f141,plain,(
% 1.47/0.55    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.47/0.55    inference(global_subsumption,[],[f53,f131])).
% 1.47/0.55  fof(f131,plain,(
% 1.47/0.55    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(resolution,[],[f55,f89])).
% 1.47/0.55  fof(f89,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.55    inference(flattening,[],[f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f17])).
% 1.47/0.55  fof(f17,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.55    inference(cnf_transformation,[],[f42])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).
% 1.47/0.55  fof(f41,plain,(
% 1.47/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.47/0.55    inference(flattening,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.47/0.55    inference(ennf_transformation,[],[f20])).
% 1.47/0.55  fof(f20,negated_conjecture,(
% 1.47/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.47/0.55    inference(negated_conjecture,[],[f19])).
% 1.47/0.55  fof(f19,conjecture,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.47/0.55  fof(f53,plain,(
% 1.47/0.55    v1_funct_1(sK3)),
% 1.47/0.55    inference(cnf_transformation,[],[f42])).
% 1.47/0.55  fof(f106,plain,(
% 1.47/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl5_2),
% 1.47/0.55    inference(avatar_component_clause,[],[f105])).
% 1.47/0.55  fof(f105,plain,(
% 1.47/0.55    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.55  fof(f1426,plain,(
% 1.47/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_24)),
% 1.47/0.55    inference(backward_demodulation,[],[f1391,f273])).
% 1.47/0.55  fof(f1391,plain,(
% 1.47/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5)),
% 1.47/0.55    inference(backward_demodulation,[],[f1313,f139])).
% 1.47/0.55  fof(f1313,plain,(
% 1.47/0.55    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl5_5),
% 1.47/0.55    inference(backward_demodulation,[],[f54,f116])).
% 1.47/0.55  fof(f116,plain,(
% 1.47/0.55    k1_xboole_0 = sK0 | ~spl5_5),
% 1.47/0.55    inference(avatar_component_clause,[],[f115])).
% 1.47/0.55  fof(f115,plain,(
% 1.47/0.55    spl5_5 <=> k1_xboole_0 = sK0),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.47/0.55  fof(f54,plain,(
% 1.47/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f42])).
% 1.47/0.55  fof(f1413,plain,(
% 1.47/0.55    ~spl5_23 | spl5_24 | ~spl5_5),
% 1.47/0.55    inference(avatar_split_clause,[],[f1411,f115,f272,f269])).
% 1.47/0.55  fof(f269,plain,(
% 1.47/0.55    spl5_23 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.47/0.55  fof(f1411,plain,(
% 1.47/0.55    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl5_5),
% 1.47/0.55    inference(resolution,[],[f1344,f69])).
% 1.47/0.55  fof(f69,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(flattening,[],[f43])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.55  fof(f1344,plain,(
% 1.47/0.55    r1_tarski(sK3,k1_xboole_0) | ~spl5_5),
% 1.47/0.55    inference(forward_demodulation,[],[f1317,f95])).
% 1.47/0.55  fof(f95,plain,(
% 1.47/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.47/0.55    inference(equality_resolution,[],[f76])).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.55    inference(flattening,[],[f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.55    inference(nnf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.47/0.55  fof(f1317,plain,(
% 1.47/0.55    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl5_5),
% 1.47/0.55    inference(backward_demodulation,[],[f134,f116])).
% 1.47/0.55  fof(f134,plain,(
% 1.47/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.47/0.55    inference(resolution,[],[f55,f73])).
% 1.47/0.55  fof(f73,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.55    inference(nnf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.55  fof(f1381,plain,(
% 1.47/0.55    spl5_9 | ~spl5_13 | ~spl5_5),
% 1.47/0.55    inference(avatar_split_clause,[],[f1379,f115,f167,f144])).
% 1.47/0.55  fof(f144,plain,(
% 1.47/0.55    spl5_9 <=> ! [X2] : ~r2_hidden(X2,sK3)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.47/0.55  fof(f167,plain,(
% 1.47/0.55    spl5_13 <=> v1_xboole_0(k1_xboole_0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.47/0.55  fof(f1379,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,sK3)) ) | ~spl5_5),
% 1.47/0.55    inference(resolution,[],[f1343,f88])).
% 1.47/0.55  fof(f88,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f36])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.55    inference(ennf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.47/0.55  fof(f1343,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_5),
% 1.47/0.55    inference(forward_demodulation,[],[f1314,f95])).
% 1.47/0.55  fof(f1314,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_5),
% 1.47/0.55    inference(backward_demodulation,[],[f55,f116])).
% 1.47/0.55  fof(f1372,plain,(
% 1.47/0.55    ~spl5_11 | spl5_12 | ~spl5_5),
% 1.47/0.55    inference(avatar_split_clause,[],[f1367,f115,f160,f157])).
% 1.47/0.55  fof(f157,plain,(
% 1.47/0.55    spl5_11 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.47/0.55  fof(f1367,plain,(
% 1.47/0.55    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl5_5),
% 1.47/0.55    inference(resolution,[],[f1315,f69])).
% 1.47/0.55  fof(f1315,plain,(
% 1.47/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl5_5),
% 1.47/0.55    inference(backward_demodulation,[],[f56,f116])).
% 1.47/0.55  fof(f56,plain,(
% 1.47/0.55    r1_tarski(sK2,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f42])).
% 1.47/0.55  fof(f1295,plain,(
% 1.47/0.55    spl5_30 | ~spl5_10),
% 1.47/0.55    inference(avatar_split_clause,[],[f531,f147,f366])).
% 1.47/0.55  fof(f366,plain,(
% 1.47/0.55    spl5_30 <=> ! [X9,X10] : ~r2_hidden(X9,k7_relat_1(sK3,X10))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.47/0.55  fof(f147,plain,(
% 1.47/0.55    spl5_10 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.47/0.55  fof(f531,plain,(
% 1.47/0.55    ( ! [X10,X9] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X9,k7_relat_1(sK3,X10))) )),
% 1.47/0.55    inference(resolution,[],[f329,f88])).
% 1.47/0.55  fof(f329,plain,(
% 1.47/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.55    inference(global_subsumption,[],[f53,f55,f328])).
% 1.47/0.55  fof(f328,plain,(
% 1.47/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(superposition,[],[f91,f141])).
% 1.47/0.55  fof(f91,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f40])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.55    inference(flattening,[],[f39])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.47/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.47/0.55  fof(f1280,plain,(
% 1.47/0.55    spl5_2 | ~spl5_73),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f1277])).
% 1.47/0.56  fof(f1277,plain,(
% 1.47/0.56    $false | (spl5_2 | ~spl5_73)),
% 1.47/0.56    inference(resolution,[],[f1105,f794])).
% 1.47/0.56  fof(f794,plain,(
% 1.47/0.56    ( ! [X2] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),sK1)) )),
% 1.47/0.56    inference(resolution,[],[f788,f73])).
% 1.47/0.56  fof(f788,plain,(
% 1.47/0.56    ( ! [X0] : (m1_subset_1(k2_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(sK1))) )),
% 1.47/0.56    inference(global_subsumption,[],[f329,f787])).
% 1.47/0.56  fof(f787,plain,(
% 1.47/0.56    ( ! [X0] : (m1_subset_1(k2_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.47/0.56    inference(superposition,[],[f81,f347])).
% 1.47/0.56  fof(f347,plain,(
% 1.47/0.56    ( ! [X1] : (k2_relset_1(sK0,sK1,k7_relat_1(sK3,X1)) = k2_relat_1(k7_relat_1(sK3,X1))) )),
% 1.47/0.56    inference(resolution,[],[f329,f79])).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.47/0.56  fof(f81,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.47/0.56  fof(f1105,plain,(
% 1.47/0.56    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl5_2 | ~spl5_73)),
% 1.47/0.56    inference(resolution,[],[f1102,f970])).
% 1.47/0.56  fof(f970,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)) ) | ~spl5_73),
% 1.47/0.56    inference(avatar_component_clause,[],[f969])).
% 1.47/0.56  fof(f969,plain,(
% 1.47/0.56    spl5_73 <=> ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 1.47/0.56  fof(f1101,plain,(
% 1.47/0.56    spl5_3 | ~spl5_74),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f1100])).
% 1.47/0.56  fof(f1100,plain,(
% 1.47/0.56    $false | (spl5_3 | ~spl5_74)),
% 1.47/0.56    inference(resolution,[],[f1056,f794])).
% 1.47/0.56  fof(f1056,plain,(
% 1.47/0.56    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl5_3 | ~spl5_74)),
% 1.47/0.56    inference(resolution,[],[f974,f953])).
% 1.47/0.56  % (31584)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  fof(f953,plain,(
% 1.47/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.47/0.56    inference(forward_demodulation,[],[f109,f141])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f108])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.47/0.56  fof(f974,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl5_74),
% 1.47/0.56    inference(avatar_component_clause,[],[f973])).
% 1.47/0.56  fof(f973,plain,(
% 1.47/0.56    spl5_74 <=> ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 1.47/0.56  fof(f985,plain,(
% 1.47/0.56    spl5_72),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f984])).
% 1.47/0.56  fof(f984,plain,(
% 1.47/0.56    $false | spl5_72),
% 1.47/0.56    inference(resolution,[],[f967,f327])).
% 1.47/0.56  fof(f327,plain,(
% 1.47/0.56    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1))) )),
% 1.47/0.56    inference(backward_demodulation,[],[f142,f141])).
% 1.47/0.56  fof(f142,plain,(
% 1.47/0.56    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 1.47/0.56    inference(global_subsumption,[],[f53,f132])).
% 1.47/0.56  fof(f132,plain,(
% 1.47/0.56    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) | ~v1_funct_1(sK3)) )),
% 1.47/0.56    inference(resolution,[],[f55,f90])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f40])).
% 1.47/0.56  fof(f967,plain,(
% 1.47/0.56    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl5_72),
% 1.47/0.56    inference(avatar_component_clause,[],[f966])).
% 1.47/0.56  fof(f966,plain,(
% 1.47/0.56    spl5_72 <=> v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 1.47/0.56  fof(f982,plain,(
% 1.47/0.56    spl5_71),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f980])).
% 1.47/0.56  fof(f980,plain,(
% 1.47/0.56    $false | spl5_71),
% 1.47/0.56    inference(resolution,[],[f964,f346])).
% 1.47/0.56  fof(f346,plain,(
% 1.47/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.47/0.56    inference(resolution,[],[f329,f78])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.56  fof(f964,plain,(
% 1.47/0.56    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl5_71),
% 1.47/0.56    inference(avatar_component_clause,[],[f963])).
% 1.47/0.56  fof(f963,plain,(
% 1.47/0.56    spl5_71 <=> v1_relat_1(k7_relat_1(sK3,sK2))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 1.47/0.56  fof(f975,plain,(
% 1.47/0.56    ~spl5_71 | ~spl5_72 | spl5_74 | ~spl5_22),
% 1.47/0.56    inference(avatar_split_clause,[],[f960,f230,f973,f966,f963])).
% 1.47/0.56  fof(f230,plain,(
% 1.47/0.56    spl5_22 <=> ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.47/0.56  fof(f960,plain,(
% 1.47/0.56    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_22),
% 1.47/0.56    inference(superposition,[],[f66,f955])).
% 1.47/0.56  fof(f955,plain,(
% 1.47/0.56    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl5_22),
% 1.47/0.56    inference(resolution,[],[f56,f231])).
% 1.47/0.56  fof(f231,plain,(
% 1.47/0.56    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl5_22),
% 1.47/0.56    inference(avatar_component_clause,[],[f230])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,axiom,(
% 1.47/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.47/0.56  fof(f971,plain,(
% 1.47/0.56    ~spl5_71 | ~spl5_72 | spl5_73 | ~spl5_22),
% 1.47/0.56    inference(avatar_split_clause,[],[f959,f230,f969,f966,f963])).
% 1.47/0.56  fof(f959,plain,(
% 1.47/0.56    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl5_22),
% 1.47/0.56    inference(superposition,[],[f65,f955])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  % (31565)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.56  fof(f946,plain,(
% 1.47/0.56    spl5_3 | ~spl5_12 | ~spl5_30),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f945])).
% 1.47/0.56  fof(f945,plain,(
% 1.47/0.56    $false | (spl5_3 | ~spl5_12 | ~spl5_30)),
% 1.47/0.56    inference(resolution,[],[f943,f541])).
% 1.47/0.56  fof(f541,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(sK3,X0),X1)) ) | ~spl5_30),
% 1.47/0.56    inference(resolution,[],[f367,f71])).
% 1.47/0.56  fof(f71,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f48])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f45])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.56  fof(f367,plain,(
% 1.47/0.56    ( ! [X10,X9] : (~r2_hidden(X9,k7_relat_1(sK3,X10))) ) | ~spl5_30),
% 1.47/0.56    inference(avatar_component_clause,[],[f366])).
% 1.47/0.56  fof(f943,plain,(
% 1.47/0.56    ~r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) | (spl5_3 | ~spl5_12)),
% 1.47/0.56    inference(resolution,[],[f941,f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f49])).
% 1.47/0.56  fof(f941,plain,(
% 1.47/0.56    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_12)),
% 1.47/0.56    inference(forward_demodulation,[],[f940,f141])).
% 1.47/0.56  fof(f940,plain,(
% 1.47/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl5_3 | ~spl5_12)),
% 1.47/0.56    inference(forward_demodulation,[],[f939,f95])).
% 1.47/0.56  fof(f939,plain,(
% 1.47/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl5_3 | ~spl5_12)),
% 1.47/0.56    inference(forward_demodulation,[],[f109,f161])).
% 1.47/0.56  fof(f696,plain,(
% 1.47/0.56    ~spl5_18 | spl5_22 | ~spl5_8),
% 1.47/0.56    inference(avatar_split_clause,[],[f693,f137,f230,f216])).
% 1.47/0.56  fof(f216,plain,(
% 1.47/0.56    spl5_18 <=> v1_relat_1(sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.47/0.56  fof(f137,plain,(
% 1.47/0.56    spl5_8 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.47/0.56  fof(f693,plain,(
% 1.47/0.56    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl5_8),
% 1.47/0.56    inference(superposition,[],[f63,f315])).
% 1.47/0.56  fof(f315,plain,(
% 1.47/0.56    sK0 = k1_relat_1(sK3) | ~spl5_8),
% 1.47/0.56    inference(forward_demodulation,[],[f128,f138])).
% 1.47/0.56  fof(f138,plain,(
% 1.47/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_8),
% 1.47/0.56    inference(avatar_component_clause,[],[f137])).
% 1.47/0.56  fof(f128,plain,(
% 1.47/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.47/0.56    inference(resolution,[],[f55,f80])).
% 1.47/0.56  fof(f80,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.47/0.56  fof(f686,plain,(
% 1.47/0.56    spl5_8 | spl5_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f685,f112,f137])).
% 1.47/0.56  fof(f685,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.56    inference(global_subsumption,[],[f54,f679])).
% 1.47/0.56  fof(f679,plain,(
% 1.47/0.56    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.47/0.56    inference(resolution,[],[f55,f82])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(nnf_transformation,[],[f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(flattening,[],[f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(ennf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.47/0.56  fof(f345,plain,(
% 1.47/0.56    ~spl5_18 | spl5_27 | ~spl5_9),
% 1.47/0.56    inference(avatar_split_clause,[],[f339,f144,f343,f216])).
% 1.47/0.56  fof(f339,plain,(
% 1.47/0.56    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl5_9),
% 1.47/0.56    inference(resolution,[],[f302,f62])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.47/0.56  fof(f302,plain,(
% 1.47/0.56    ( ! [X1] : (~r1_tarski(X1,sK3) | sK3 = X1) ) | ~spl5_9),
% 1.47/0.56    inference(resolution,[],[f262,f69])).
% 1.47/0.56  fof(f262,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl5_9),
% 1.47/0.56    inference(resolution,[],[f145,f71])).
% 1.47/0.56  fof(f145,plain,(
% 1.47/0.56    ( ! [X2] : (~r2_hidden(X2,sK3)) ) | ~spl5_9),
% 1.47/0.56    inference(avatar_component_clause,[],[f144])).
% 1.47/0.56  fof(f304,plain,(
% 1.47/0.56    spl5_23),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f303])).
% 1.47/0.56  fof(f303,plain,(
% 1.47/0.56    $false | spl5_23),
% 1.47/0.56    inference(resolution,[],[f270,f60])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.47/0.56  fof(f270,plain,(
% 1.47/0.56    ~r1_tarski(k1_xboole_0,sK3) | spl5_23),
% 1.47/0.56    inference(avatar_component_clause,[],[f269])).
% 1.47/0.56  fof(f255,plain,(
% 1.47/0.56    ~spl5_5 | spl5_10),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f254])).
% 1.47/0.56  fof(f254,plain,(
% 1.47/0.56    $false | (~spl5_5 | spl5_10)),
% 1.47/0.56    inference(subsumption_resolution,[],[f59,f247])).
% 1.47/0.56  fof(f247,plain,(
% 1.47/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl5_5 | spl5_10)),
% 1.47/0.56    inference(forward_demodulation,[],[f243,f95])).
% 1.47/0.56  fof(f243,plain,(
% 1.47/0.56    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl5_5 | spl5_10)),
% 1.47/0.56    inference(backward_demodulation,[],[f148,f116])).
% 1.47/0.56  fof(f148,plain,(
% 1.47/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_10),
% 1.47/0.56    inference(avatar_component_clause,[],[f147])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    v1_xboole_0(k1_xboole_0)),
% 1.47/0.56    inference(cnf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    v1_xboole_0(k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.47/0.56  fof(f234,plain,(
% 1.47/0.56    spl5_18),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f233])).
% 1.47/0.56  fof(f233,plain,(
% 1.47/0.56    $false | spl5_18),
% 1.47/0.56    inference(subsumption_resolution,[],[f126,f217])).
% 1.47/0.56  fof(f217,plain,(
% 1.47/0.56    ~v1_relat_1(sK3) | spl5_18),
% 1.47/0.56    inference(avatar_component_clause,[],[f216])).
% 1.47/0.56  fof(f126,plain,(
% 1.47/0.56    v1_relat_1(sK3)),
% 1.47/0.56    inference(resolution,[],[f55,f78])).
% 1.47/0.56  fof(f199,plain,(
% 1.47/0.56    spl5_1),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f198])).
% 1.47/0.56  fof(f198,plain,(
% 1.47/0.56    $false | spl5_1),
% 1.47/0.56    inference(subsumption_resolution,[],[f103,f142])).
% 1.47/0.56  fof(f103,plain,(
% 1.47/0.56    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl5_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f102])).
% 1.47/0.56  fof(f102,plain,(
% 1.47/0.56    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.47/0.56  fof(f189,plain,(
% 1.47/0.56    spl5_11),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f188])).
% 1.47/0.56  fof(f188,plain,(
% 1.47/0.56    $false | spl5_11),
% 1.47/0.56    inference(resolution,[],[f158,f60])).
% 1.47/0.56  fof(f158,plain,(
% 1.47/0.56    ~r1_tarski(k1_xboole_0,sK2) | spl5_11),
% 1.47/0.56    inference(avatar_component_clause,[],[f157])).
% 1.47/0.56  fof(f171,plain,(
% 1.47/0.56    spl5_13),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f170])).
% 1.47/0.56  fof(f170,plain,(
% 1.47/0.56    $false | spl5_13),
% 1.47/0.56    inference(subsumption_resolution,[],[f59,f168])).
% 1.47/0.56  fof(f168,plain,(
% 1.47/0.56    ~v1_xboole_0(k1_xboole_0) | spl5_13),
% 1.47/0.56    inference(avatar_component_clause,[],[f167])).
% 1.47/0.56  fof(f117,plain,(
% 1.47/0.56    ~spl5_4 | spl5_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f57,f115,f112])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f58,f108,f105,f102])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (31558)------------------------------
% 1.47/0.56  % (31558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (31558)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (31558)Memory used [KB]: 11513
% 1.47/0.56  % (31558)Time elapsed: 0.148 s
% 1.47/0.56  % (31558)------------------------------
% 1.47/0.56  % (31558)------------------------------
% 1.61/0.56  % (31550)Success in time 0.211 s
%------------------------------------------------------------------------------
