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
% DateTime   : Thu Dec  3 13:03:09 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 757 expanded)
%              Number of leaves         :   28 ( 198 expanded)
%              Depth                    :   18
%              Number of atoms          :  548 (4365 expanded)
%              Number of equality atoms :  118 (1048 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f113,f161,f329,f558,f613,f930,f1104,f1297,f1319,f1326,f1333,f1365,f1414,f1509])).

fof(f1509,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f1508])).

fof(f1508,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f1503,f1449])).

fof(f1449,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f1423,f314])).

fof(f314,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(resolution,[],[f293,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f293,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f279,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f279,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f130,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f130,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40])).

fof(f40,plain,
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f1423,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1378,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1378,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f50,f107])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f1503,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f1017,f1483])).

fof(f1483,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f1482,f56])).

fof(f1482,plain,
    ( r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1481,f314])).

fof(f1481,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1402,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f298,f56])).

fof(f298,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f52,f112])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1402,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1392,f85])).

fof(f1392,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f1342,f107])).

fof(f1342,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f1334,f65])).

fof(f1334,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f102,f133])).

fof(f133,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f102,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1017,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f1016,f314])).

fof(f1016,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f791,f107])).

fof(f791,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f168,f310])).

fof(f310,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl4_23
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f168,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f99,f133])).

fof(f99,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1414,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1413,f110,f308,f304])).

fof(f304,plain,
    ( spl4_22
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1413,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f1407,f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1407,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f52,f112])).

fof(f1365,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f1364])).

fof(f1364,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1363,f1334])).

fof(f1363,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1362,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1362,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1361,f168])).

fof(f1361,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f1360])).

fof(f1360,plain,
    ( sK2 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(superposition,[],[f76,f1346])).

fof(f1346,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1340,f383])).

fof(f383,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_21 ),
    inference(resolution,[],[f359,f52])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f358,f129])).

fof(f129,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f358,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl4_21 ),
    inference(superposition,[],[f59,f357])).

fof(f357,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f128,f274])).

fof(f274,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_21
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f128,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1340,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f1334,f72])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f1333,plain,
    ( ~ spl4_21
    | spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1332])).

fof(f1332,plain,
    ( $false
    | ~ spl4_21
    | spl4_54 ),
    inference(subsumption_resolution,[],[f1331,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1331,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl4_21
    | spl4_54 ),
    inference(forward_demodulation,[],[f1330,f383])).

fof(f1330,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_54 ),
    inference(forward_demodulation,[],[f1292,f133])).

fof(f1292,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f1290,plain,
    ( spl4_54
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1326,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f1325])).

fof(f1325,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f1324,f198])).

fof(f198,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f197,f177])).

fof(f177,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f171,f71])).

fof(f171,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f169,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f82,f133])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f197,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f175,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f175,plain,(
    ! [X5] : v5_relat_1(k7_relat_1(sK3,X5),sK1) ),
    inference(resolution,[],[f171,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1324,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_55 ),
    inference(forward_demodulation,[],[f1296,f133])).

fof(f1296,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1294,plain,
    ( spl4_55
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1319,plain,(
    spl4_53 ),
    inference(avatar_contradiction_clause,[],[f1318])).

fof(f1318,plain,
    ( $false
    | spl4_53 ),
    inference(subsumption_resolution,[],[f1313,f177])).

fof(f1313,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_53 ),
    inference(backward_demodulation,[],[f1288,f133])).

fof(f1288,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f1286])).

fof(f1286,plain,
    ( spl4_53
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1297,plain,
    ( ~ spl4_53
    | ~ spl4_54
    | ~ spl4_55
    | spl4_3 ),
    inference(avatar_split_clause,[],[f1283,f101,f1294,f1290,f1286])).

fof(f1283,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_3 ),
    inference(resolution,[],[f103,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f103,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1104,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f1103,f120,f116])).

fof(f116,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f120,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1103,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f52,f64])).

fof(f930,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f928,f49])).

fof(f928,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f925,f51])).

fof(f925,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f922,f82])).

fof(f922,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f103,f122])).

fof(f122,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f613,plain,
    ( ~ spl4_5
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | ~ spl4_5
    | spl4_22 ),
    inference(subsumption_resolution,[],[f609,f84])).

fof(f609,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_22 ),
    inference(backward_demodulation,[],[f306,f301])).

fof(f306,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f304])).

fof(f558,plain,
    ( spl4_21
    | spl4_4 ),
    inference(avatar_split_clause,[],[f347,f106,f272])).

fof(f347,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f339,f50])).

fof(f339,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f329,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f326,f84])).

fof(f326,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f299,f301])).

fof(f299,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f118,f112])).

fof(f118,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f161,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f132,f95])).

fof(f95,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f132,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f53,f110,f106])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f101,f97,f93])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (21756)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (21757)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (21735)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (21749)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (21741)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (21738)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (21737)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (21751)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (21743)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (21747)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (21759)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (21739)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (21752)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (21753)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (21748)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21750)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (21736)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21758)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (21742)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (21754)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (21740)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (21755)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (21745)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (21760)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (21746)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (21744)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.71/0.59  % (21736)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f1512,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(avatar_sat_refutation,[],[f104,f113,f161,f329,f558,f613,f930,f1104,f1297,f1319,f1326,f1333,f1365,f1414,f1509])).
% 1.71/0.59  fof(f1509,plain,(
% 1.71/0.59    spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_23),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f1508])).
% 1.71/0.59  fof(f1508,plain,(
% 1.71/0.59    $false | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_23)),
% 1.71/0.59    inference(subsumption_resolution,[],[f1503,f1449])).
% 1.71/0.59  fof(f1449,plain,(
% 1.71/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.71/0.59    inference(backward_demodulation,[],[f1423,f314])).
% 1.71/0.59  fof(f314,plain,(
% 1.71/0.59    k1_xboole_0 = sK3 | ~spl4_4),
% 1.71/0.59    inference(resolution,[],[f293,f56])).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f23])).
% 1.71/0.59  fof(f23,plain,(
% 1.71/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.71/0.59    inference(ennf_transformation,[],[f2])).
% 1.71/0.59  fof(f2,axiom,(
% 1.71/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.71/0.59  fof(f293,plain,(
% 1.71/0.59    r1_tarski(sK3,k1_xboole_0) | ~spl4_4),
% 1.71/0.59    inference(forward_demodulation,[],[f279,f85])).
% 1.71/0.59  fof(f85,plain,(
% 1.71/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.71/0.59    inference(equality_resolution,[],[f69])).
% 1.71/0.59  fof(f69,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.71/0.59    inference(cnf_transformation,[],[f47])).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.59    inference(flattening,[],[f46])).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.59    inference(nnf_transformation,[],[f3])).
% 1.71/0.59  fof(f3,axiom,(
% 1.71/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.59  fof(f279,plain,(
% 1.71/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl4_4),
% 1.71/0.59    inference(backward_demodulation,[],[f130,f107])).
% 1.71/0.59  fof(f107,plain,(
% 1.71/0.59    k1_xboole_0 = sK1 | ~spl4_4),
% 1.71/0.59    inference(avatar_component_clause,[],[f106])).
% 1.71/0.59  fof(f106,plain,(
% 1.71/0.59    spl4_4 <=> k1_xboole_0 = sK1),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.59  fof(f130,plain,(
% 1.71/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.71/0.59    inference(resolution,[],[f51,f65])).
% 1.71/0.59  fof(f65,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f45])).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.59    inference(nnf_transformation,[],[f4])).
% 1.71/0.59  fof(f4,axiom,(
% 1.71/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.59  fof(f51,plain,(
% 1.71/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.59    inference(cnf_transformation,[],[f41])).
% 1.71/0.59  fof(f41,plain,(
% 1.71/0.59    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.71/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f40])).
% 1.71/0.59  fof(f40,plain,(
% 1.71/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f21,plain,(
% 1.71/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.71/0.59    inference(flattening,[],[f20])).
% 1.71/0.59  fof(f20,plain,(
% 1.71/0.59    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.71/0.59    inference(ennf_transformation,[],[f18])).
% 1.71/0.59  fof(f18,negated_conjecture,(
% 1.71/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.59    inference(negated_conjecture,[],[f17])).
% 1.71/0.59  fof(f17,conjecture,(
% 1.71/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.71/0.59  fof(f1423,plain,(
% 1.71/0.59    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.71/0.59    inference(forward_demodulation,[],[f1378,f112])).
% 1.71/0.59  fof(f112,plain,(
% 1.71/0.59    k1_xboole_0 = sK0 | ~spl4_5),
% 1.71/0.59    inference(avatar_component_clause,[],[f110])).
% 1.71/0.59  fof(f110,plain,(
% 1.71/0.59    spl4_5 <=> k1_xboole_0 = sK0),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.59  fof(f1378,plain,(
% 1.71/0.59    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.71/0.59    inference(backward_demodulation,[],[f50,f107])).
% 1.71/0.59  fof(f50,plain,(
% 1.71/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f41])).
% 1.71/0.59  fof(f1503,plain,(
% 1.71/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_23)),
% 1.71/0.59    inference(backward_demodulation,[],[f1017,f1483])).
% 1.71/0.59  fof(f1483,plain,(
% 1.71/0.59    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.71/0.59    inference(resolution,[],[f1482,f56])).
% 1.71/0.59  fof(f1482,plain,(
% 1.71/0.59    r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.71/0.59    inference(forward_demodulation,[],[f1481,f314])).
% 1.71/0.59  fof(f1481,plain,(
% 1.71/0.59    r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.71/0.59    inference(forward_demodulation,[],[f1402,f301])).
% 1.71/0.59  fof(f301,plain,(
% 1.71/0.59    k1_xboole_0 = sK2 | ~spl4_5),
% 1.71/0.59    inference(resolution,[],[f298,f56])).
% 1.71/0.59  fof(f298,plain,(
% 1.71/0.59    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.71/0.59    inference(backward_demodulation,[],[f52,f112])).
% 1.71/0.59  fof(f52,plain,(
% 1.71/0.59    r1_tarski(sK2,sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f41])).
% 1.71/0.59  fof(f1402,plain,(
% 1.71/0.59    r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) | (~spl4_3 | ~spl4_4)),
% 1.71/0.59    inference(forward_demodulation,[],[f1392,f85])).
% 1.71/0.59  fof(f1392,plain,(
% 1.71/0.59    r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.71/0.59    inference(backward_demodulation,[],[f1342,f107])).
% 1.71/0.59  fof(f1342,plain,(
% 1.71/0.59    r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) | ~spl4_3),
% 1.71/0.59    inference(resolution,[],[f1334,f65])).
% 1.71/0.59  fof(f1334,plain,(
% 1.71/0.59    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.71/0.59    inference(forward_demodulation,[],[f102,f133])).
% 1.71/0.59  fof(f133,plain,(
% 1.71/0.59    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f125,f49])).
% 1.71/0.59  fof(f49,plain,(
% 1.71/0.59    v1_funct_1(sK3)),
% 1.71/0.59    inference(cnf_transformation,[],[f41])).
% 1.71/0.59  fof(f125,plain,(
% 1.71/0.59    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.71/0.59    inference(resolution,[],[f51,f80])).
% 1.71/0.59  fof(f80,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f37])).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.59    inference(flattening,[],[f36])).
% 1.71/0.59  fof(f36,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.59    inference(ennf_transformation,[],[f16])).
% 1.71/0.59  fof(f16,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.71/0.59  fof(f102,plain,(
% 1.71/0.59    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.71/0.59    inference(avatar_component_clause,[],[f101])).
% 1.71/0.59  fof(f101,plain,(
% 1.71/0.59    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.59  fof(f1017,plain,(
% 1.71/0.59    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_23)),
% 1.71/0.59    inference(forward_demodulation,[],[f1016,f314])).
% 1.71/0.59  fof(f1016,plain,(
% 1.71/0.59    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_23)),
% 1.71/0.59    inference(forward_demodulation,[],[f791,f107])).
% 1.71/0.59  fof(f791,plain,(
% 1.71/0.59    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_23)),
% 1.71/0.59    inference(forward_demodulation,[],[f168,f310])).
% 1.71/0.59  fof(f310,plain,(
% 1.71/0.59    k1_xboole_0 = sK2 | ~spl4_23),
% 1.71/0.59    inference(avatar_component_clause,[],[f308])).
% 1.71/0.59  fof(f308,plain,(
% 1.71/0.59    spl4_23 <=> k1_xboole_0 = sK2),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.71/0.59  fof(f168,plain,(
% 1.71/0.59    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.71/0.59    inference(backward_demodulation,[],[f99,f133])).
% 1.71/0.59  fof(f99,plain,(
% 1.71/0.59    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.71/0.59    inference(avatar_component_clause,[],[f97])).
% 1.71/0.59  fof(f97,plain,(
% 1.71/0.59    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.59  fof(f1414,plain,(
% 1.71/0.59    ~spl4_22 | spl4_23 | ~spl4_5),
% 1.71/0.59    inference(avatar_split_clause,[],[f1413,f110,f308,f304])).
% 1.71/0.59  fof(f304,plain,(
% 1.71/0.59    spl4_22 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.71/0.59  fof(f1413,plain,(
% 1.71/0.59    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_5),
% 1.71/0.59    inference(resolution,[],[f1407,f64])).
% 1.71/0.59  fof(f64,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f44])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.59    inference(flattening,[],[f43])).
% 1.71/0.59  fof(f43,plain,(
% 1.71/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.59    inference(nnf_transformation,[],[f1])).
% 1.71/0.59  fof(f1,axiom,(
% 1.71/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.59  fof(f1407,plain,(
% 1.71/0.59    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.71/0.59    inference(backward_demodulation,[],[f52,f112])).
% 1.71/0.59  fof(f1365,plain,(
% 1.71/0.59    spl4_2 | ~spl4_3 | spl4_4 | ~spl4_21),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f1364])).
% 1.71/0.59  fof(f1364,plain,(
% 1.71/0.59    $false | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_21)),
% 1.71/0.59    inference(subsumption_resolution,[],[f1363,f1334])).
% 1.71/0.59  fof(f1363,plain,(
% 1.71/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_21)),
% 1.71/0.59    inference(subsumption_resolution,[],[f1362,f108])).
% 1.71/0.59  fof(f108,plain,(
% 1.71/0.59    k1_xboole_0 != sK1 | spl4_4),
% 1.71/0.59    inference(avatar_component_clause,[],[f106])).
% 1.71/0.59  fof(f1362,plain,(
% 1.71/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | ~spl4_21)),
% 1.71/0.59    inference(subsumption_resolution,[],[f1361,f168])).
% 1.71/0.59  fof(f1361,plain,(
% 1.71/0.59    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_21)),
% 1.71/0.59    inference(trivial_inequality_removal,[],[f1360])).
% 1.71/0.59  fof(f1360,plain,(
% 1.71/0.59    sK2 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_21)),
% 1.71/0.59    inference(superposition,[],[f76,f1346])).
% 1.71/0.59  fof(f1346,plain,(
% 1.71/0.59    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_21)),
% 1.71/0.59    inference(forward_demodulation,[],[f1340,f383])).
% 1.71/0.59  fof(f383,plain,(
% 1.71/0.59    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_21),
% 1.71/0.59    inference(resolution,[],[f359,f52])).
% 1.71/0.59  fof(f359,plain,(
% 1.71/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_21),
% 1.71/0.59    inference(subsumption_resolution,[],[f358,f129])).
% 1.71/0.59  fof(f129,plain,(
% 1.71/0.59    v1_relat_1(sK3)),
% 1.71/0.59    inference(resolution,[],[f51,f71])).
% 1.71/0.59  fof(f71,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f31])).
% 1.71/0.59  fof(f31,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f10])).
% 1.71/0.59  fof(f10,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.59  fof(f358,plain,(
% 1.71/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl4_21),
% 1.71/0.59    inference(superposition,[],[f59,f357])).
% 1.71/0.59  fof(f357,plain,(
% 1.71/0.59    sK0 = k1_relat_1(sK3) | ~spl4_21),
% 1.71/0.59    inference(forward_demodulation,[],[f128,f274])).
% 1.71/0.59  fof(f274,plain,(
% 1.71/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_21),
% 1.71/0.59    inference(avatar_component_clause,[],[f272])).
% 1.71/0.59  fof(f272,plain,(
% 1.71/0.59    spl4_21 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.71/0.59  fof(f128,plain,(
% 1.71/0.59    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.71/0.59    inference(resolution,[],[f51,f72])).
% 1.71/0.59  fof(f72,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f32])).
% 1.71/0.59  fof(f32,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f12])).
% 1.71/0.59  fof(f12,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.59  fof(f59,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.71/0.59    inference(flattening,[],[f26])).
% 1.71/0.59  fof(f26,plain,(
% 1.71/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f9])).
% 1.71/0.59  fof(f9,axiom,(
% 1.71/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.71/0.59  fof(f1340,plain,(
% 1.71/0.59    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_3),
% 1.71/0.59    inference(resolution,[],[f1334,f72])).
% 1.71/0.59  fof(f76,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f48])).
% 1.71/0.59  fof(f48,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(nnf_transformation,[],[f35])).
% 1.71/0.59  fof(f35,plain,(
% 1.71/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(flattening,[],[f34])).
% 1.71/0.59  fof(f34,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f14])).
% 1.71/0.59  fof(f14,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.59  fof(f1333,plain,(
% 1.71/0.59    ~spl4_21 | spl4_54),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f1332])).
% 1.71/0.59  fof(f1332,plain,(
% 1.71/0.59    $false | (~spl4_21 | spl4_54)),
% 1.71/0.59    inference(subsumption_resolution,[],[f1331,f84])).
% 1.71/0.59  fof(f84,plain,(
% 1.71/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.59    inference(equality_resolution,[],[f62])).
% 1.71/0.59  fof(f62,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.71/0.59    inference(cnf_transformation,[],[f44])).
% 1.71/0.59  fof(f1331,plain,(
% 1.71/0.59    ~r1_tarski(sK2,sK2) | (~spl4_21 | spl4_54)),
% 1.71/0.59    inference(forward_demodulation,[],[f1330,f383])).
% 1.71/0.59  fof(f1330,plain,(
% 1.71/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_54),
% 1.71/0.59    inference(forward_demodulation,[],[f1292,f133])).
% 1.71/0.59  fof(f1292,plain,(
% 1.71/0.59    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_54),
% 1.71/0.59    inference(avatar_component_clause,[],[f1290])).
% 1.71/0.59  fof(f1290,plain,(
% 1.71/0.59    spl4_54 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.71/0.59  fof(f1326,plain,(
% 1.71/0.59    spl4_55),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f1325])).
% 1.71/0.59  fof(f1325,plain,(
% 1.71/0.59    $false | spl4_55),
% 1.71/0.59    inference(subsumption_resolution,[],[f1324,f198])).
% 1.71/0.59  fof(f198,plain,(
% 1.71/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f197,f177])).
% 1.71/0.59  fof(f177,plain,(
% 1.71/0.59    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 1.71/0.59    inference(resolution,[],[f171,f71])).
% 1.71/0.59  fof(f171,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f170,f49])).
% 1.71/0.59  fof(f170,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f169,f51])).
% 1.71/0.59  fof(f169,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.71/0.59    inference(superposition,[],[f82,f133])).
% 1.71/0.59  fof(f82,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f39])).
% 1.71/0.59  fof(f39,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.59    inference(flattening,[],[f38])).
% 1.71/0.59  fof(f38,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.59    inference(ennf_transformation,[],[f15])).
% 1.71/0.59  fof(f15,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.71/0.59  fof(f197,plain,(
% 1.71/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.71/0.59    inference(resolution,[],[f175,f60])).
% 1.71/0.59  fof(f60,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f42])).
% 1.71/0.59  fof(f42,plain,(
% 1.71/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.59    inference(nnf_transformation,[],[f28])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.71/0.59  fof(f175,plain,(
% 1.71/0.59    ( ! [X5] : (v5_relat_1(k7_relat_1(sK3,X5),sK1)) )),
% 1.71/0.59    inference(resolution,[],[f171,f73])).
% 1.71/0.59  fof(f73,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f33])).
% 1.71/0.59  fof(f33,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.71/0.59    inference(pure_predicate_removal,[],[f11])).
% 1.71/0.59  fof(f11,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.59  fof(f1324,plain,(
% 1.71/0.59    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_55),
% 1.71/0.59    inference(forward_demodulation,[],[f1296,f133])).
% 1.71/0.59  fof(f1296,plain,(
% 1.71/0.59    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_55),
% 1.71/0.59    inference(avatar_component_clause,[],[f1294])).
% 1.71/0.59  fof(f1294,plain,(
% 1.71/0.59    spl4_55 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.71/0.59  fof(f1319,plain,(
% 1.71/0.59    spl4_53),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f1318])).
% 1.71/0.59  fof(f1318,plain,(
% 1.71/0.59    $false | spl4_53),
% 1.71/0.59    inference(subsumption_resolution,[],[f1313,f177])).
% 1.71/0.59  fof(f1313,plain,(
% 1.71/0.59    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_53),
% 1.71/0.59    inference(backward_demodulation,[],[f1288,f133])).
% 1.71/0.59  fof(f1288,plain,(
% 1.71/0.59    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_53),
% 1.71/0.59    inference(avatar_component_clause,[],[f1286])).
% 1.71/0.59  fof(f1286,plain,(
% 1.71/0.59    spl4_53 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.71/0.59  fof(f1297,plain,(
% 1.71/0.59    ~spl4_53 | ~spl4_54 | ~spl4_55 | spl4_3),
% 1.71/0.59    inference(avatar_split_clause,[],[f1283,f101,f1294,f1290,f1286])).
% 1.71/0.59  fof(f1283,plain,(
% 1.71/0.59    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_3),
% 1.71/0.59    inference(resolution,[],[f103,f70])).
% 1.71/0.62  fof(f70,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f30])).
% 1.71/0.62  fof(f30,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.71/0.62    inference(flattening,[],[f29])).
% 1.71/0.62  fof(f29,plain,(
% 1.71/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.71/0.62    inference(ennf_transformation,[],[f13])).
% 1.71/0.62  fof(f13,axiom,(
% 1.71/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.71/0.62  fof(f103,plain,(
% 1.71/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.71/0.62    inference(avatar_component_clause,[],[f101])).
% 1.71/0.62  fof(f1104,plain,(
% 1.71/0.62    ~spl4_6 | spl4_7),
% 1.71/0.62    inference(avatar_split_clause,[],[f1103,f120,f116])).
% 1.71/0.62  fof(f116,plain,(
% 1.71/0.62    spl4_6 <=> r1_tarski(sK0,sK2)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.62  fof(f120,plain,(
% 1.71/0.62    spl4_7 <=> sK0 = sK2),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.62  fof(f1103,plain,(
% 1.71/0.62    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.71/0.62    inference(resolution,[],[f52,f64])).
% 1.71/0.62  fof(f930,plain,(
% 1.71/0.62    spl4_3 | ~spl4_7),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f929])).
% 1.71/0.62  fof(f929,plain,(
% 1.71/0.62    $false | (spl4_3 | ~spl4_7)),
% 1.71/0.62    inference(subsumption_resolution,[],[f928,f49])).
% 1.71/0.62  fof(f928,plain,(
% 1.71/0.62    ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.71/0.62    inference(subsumption_resolution,[],[f925,f51])).
% 1.71/0.62  fof(f925,plain,(
% 1.71/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.71/0.62    inference(resolution,[],[f922,f82])).
% 1.71/0.62  fof(f922,plain,(
% 1.71/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 1.71/0.62    inference(forward_demodulation,[],[f103,f122])).
% 1.71/0.62  fof(f122,plain,(
% 1.71/0.62    sK0 = sK2 | ~spl4_7),
% 1.71/0.62    inference(avatar_component_clause,[],[f120])).
% 1.71/0.62  fof(f613,plain,(
% 1.71/0.62    ~spl4_5 | spl4_22),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f612])).
% 1.71/0.62  fof(f612,plain,(
% 1.71/0.62    $false | (~spl4_5 | spl4_22)),
% 1.71/0.62    inference(subsumption_resolution,[],[f609,f84])).
% 1.71/0.62  fof(f609,plain,(
% 1.71/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_22)),
% 1.71/0.62    inference(backward_demodulation,[],[f306,f301])).
% 1.71/0.62  fof(f306,plain,(
% 1.71/0.62    ~r1_tarski(k1_xboole_0,sK2) | spl4_22),
% 1.71/0.62    inference(avatar_component_clause,[],[f304])).
% 1.71/0.62  fof(f558,plain,(
% 1.71/0.62    spl4_21 | spl4_4),
% 1.71/0.62    inference(avatar_split_clause,[],[f347,f106,f272])).
% 1.71/0.62  fof(f347,plain,(
% 1.71/0.62    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.62    inference(subsumption_resolution,[],[f339,f50])).
% 1.71/0.62  fof(f339,plain,(
% 1.71/0.62    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.62    inference(resolution,[],[f51,f74])).
% 1.71/0.62  fof(f74,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.71/0.62    inference(cnf_transformation,[],[f48])).
% 1.71/0.62  fof(f329,plain,(
% 1.71/0.62    ~spl4_5 | spl4_6),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f328])).
% 1.71/0.62  fof(f328,plain,(
% 1.71/0.62    $false | (~spl4_5 | spl4_6)),
% 1.71/0.62    inference(subsumption_resolution,[],[f326,f84])).
% 1.71/0.62  fof(f326,plain,(
% 1.71/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_6)),
% 1.71/0.62    inference(backward_demodulation,[],[f299,f301])).
% 1.71/0.62  fof(f299,plain,(
% 1.71/0.62    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 1.71/0.62    inference(backward_demodulation,[],[f118,f112])).
% 1.71/0.62  fof(f118,plain,(
% 1.71/0.62    ~r1_tarski(sK0,sK2) | spl4_6),
% 1.71/0.62    inference(avatar_component_clause,[],[f116])).
% 1.71/0.62  fof(f161,plain,(
% 1.71/0.62    spl4_1),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f160])).
% 1.71/0.62  fof(f160,plain,(
% 1.71/0.62    $false | spl4_1),
% 1.71/0.62    inference(resolution,[],[f132,f95])).
% 1.71/0.62  fof(f95,plain,(
% 1.71/0.62    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.71/0.62    inference(avatar_component_clause,[],[f93])).
% 1.71/0.62  fof(f93,plain,(
% 1.71/0.62    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.62  fof(f132,plain,(
% 1.71/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.71/0.62    inference(subsumption_resolution,[],[f124,f49])).
% 1.71/0.62  fof(f124,plain,(
% 1.71/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.71/0.62    inference(resolution,[],[f51,f81])).
% 1.71/0.62  fof(f81,plain,(
% 1.71/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f39])).
% 1.71/0.62  fof(f113,plain,(
% 1.71/0.62    ~spl4_4 | spl4_5),
% 1.71/0.62    inference(avatar_split_clause,[],[f53,f110,f106])).
% 1.71/0.62  fof(f53,plain,(
% 1.71/0.62    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.71/0.62    inference(cnf_transformation,[],[f41])).
% 1.71/0.62  fof(f104,plain,(
% 1.71/0.62    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.71/0.62    inference(avatar_split_clause,[],[f54,f101,f97,f93])).
% 1.71/0.62  fof(f54,plain,(
% 1.71/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.62    inference(cnf_transformation,[],[f41])).
% 1.71/0.62  % SZS output end Proof for theBenchmark
% 1.71/0.62  % (21736)------------------------------
% 1.71/0.62  % (21736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.62  % (21736)Termination reason: Refutation
% 1.71/0.62  
% 1.71/0.62  % (21736)Memory used [KB]: 11129
% 1.71/0.62  % (21736)Time elapsed: 0.173 s
% 1.71/0.62  % (21736)------------------------------
% 1.71/0.62  % (21736)------------------------------
% 1.71/0.62  % (21732)Success in time 0.265 s
%------------------------------------------------------------------------------
