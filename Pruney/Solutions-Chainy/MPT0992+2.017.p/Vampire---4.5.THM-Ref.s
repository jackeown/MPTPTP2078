%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 821 expanded)
%              Number of leaves         :   28 ( 211 expanded)
%              Depth                    :   17
%              Number of atoms          :  563 (4577 expanded)
%              Number of equality atoms :  107 (1048 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f188,f356,f400,f462,f1064,f1174,f1196,f1201,f1384,f1418])).

fof(f1418,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1417])).

fof(f1417,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f1414,f1347])).

fof(f1347,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f1323,f372])).

fof(f372,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f371,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f371,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f368,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f368,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(resolution,[],[f367,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f367,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f366,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f366,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f58,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f47])).

fof(f47,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1323,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1203,f125])).

fof(f1203,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f57,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1414,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f1391,f1408])).

fof(f1408,plain,
    ( ! [X2] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f1407,f64])).

fof(f1407,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
        | ~ r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X2)) )
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(resolution,[],[f1405,f77])).

fof(f1405,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f1404,f357])).

fof(f357,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f136,f125])).

fof(f136,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1404,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f185,f125])).

fof(f185,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_13
  <=> ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1391,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1390,f372])).

fof(f1390,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f337,f357])).

fof(f337,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f215,f120])).

fof(f215,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f112,f147])).

fof(f147,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f139,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f139,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f58,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f112,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1384,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1382,f375])).

fof(f375,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f143,f372])).

fof(f143,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f58,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1382,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f1371,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1371,plain,
    ( ~ r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f1363,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1363,plain,
    ( ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1362,f372])).

fof(f1362,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1289,f357])).

fof(f1289,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1252,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1252,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f1065,f120])).

fof(f1065,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f116,f147])).

fof(f116,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1201,plain,
    ( ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f435,f184,f180])).

fof(f180,plain,
    ( spl4_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f435,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK2,X0),sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f127,f67])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f59,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f59,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f1196,plain,
    ( spl4_26
    | spl4_4 ),
    inference(avatar_split_clause,[],[f475,f119,f322])).

fof(f322,plain,
    ( spl4_26
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f475,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f467,f57])).

fof(f467,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f58,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f1174,plain,
    ( spl4_3
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f1173])).

fof(f1173,plain,
    ( $false
    | spl4_3
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f1162,f205])).

fof(f205,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f200,f143])).

fof(f200,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f153,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK3))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f151,f92])).

fof(f151,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f150,f143])).

fof(f150,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f141,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f141,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1162,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_26 ),
    inference(resolution,[],[f625,f1065])).

fof(f625,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f624,f243])).

fof(f243,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f218,f83])).

fof(f218,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f217,f56])).

fof(f217,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f95,f147])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f624,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f620,f214])).

fof(f214,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f146,f147])).

fof(f146,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f138,f56])).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f58,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f620,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_26 ),
    inference(superposition,[],[f74,f612])).

fof(f612,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_26 ),
    inference(resolution,[],[f548,f59])).

fof(f548,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f543,f143])).

fof(f543,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_26 ),
    inference(superposition,[],[f69,f540])).

fof(f540,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f142,f324])).

fof(f324,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f322])).

fof(f142,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1064,plain,
    ( spl4_2
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f1063])).

fof(f1063,plain,
    ( $false
    | spl4_2
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f1042,f215])).

fof(f1042,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_26 ),
    inference(resolution,[],[f623,f205])).

fof(f623,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f622,f243])).

fof(f622,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f619,f214])).

fof(f619,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_26 ),
    inference(superposition,[],[f73,f612])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f462,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f461,f134,f130])).

fof(f130,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f461,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f59,f77])).

fof(f400,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(subsumption_resolution,[],[f365,f375])).

fof(f365,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(backward_demodulation,[],[f182,f357])).

fof(f182,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f356,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f353,f64])).

fof(f353,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f132,f125])).

fof(f132,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f188,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f146,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f126,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f60,f123,f119])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f61,f114,f110,f106])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14900)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (14891)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (14908)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (14901)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (14896)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (14890)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (14906)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (14907)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (14910)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (14887)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14897)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (14899)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (14888)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (14889)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (14895)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (14903)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (14904)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (14902)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (14911)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (14894)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (14898)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (14909)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (14886)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (14905)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (14913)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.55  % (14912)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.56  % (14887)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f1419,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f117,f126,f188,f356,f400,f462,f1064,f1174,f1196,f1201,f1384,f1418])).
% 0.20/0.56  fof(f1418,plain,(
% 0.20/0.56    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_13),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f1417])).
% 0.20/0.56  fof(f1417,plain,(
% 0.20/0.56    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_13)),
% 0.20/0.56    inference(subsumption_resolution,[],[f1414,f1347])).
% 0.20/0.56  fof(f1347,plain,(
% 0.20/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.20/0.56    inference(backward_demodulation,[],[f1323,f372])).
% 0.20/0.56  fof(f372,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | ~spl4_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f371,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.56  fof(f371,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl4_5),
% 0.20/0.56    inference(resolution,[],[f368,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f368,plain,(
% 0.20/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 0.20/0.56    inference(resolution,[],[f367,f78])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f367,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 0.20/0.56    inference(forward_demodulation,[],[f366,f99])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f81])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(flattening,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.56  fof(f366,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_5),
% 0.20/0.56    inference(forward_demodulation,[],[f58,f125])).
% 0.20/0.56  fof(f125,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl4_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f123])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    spl4_5 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.56    inference(flattening,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.56    inference(ennf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.56    inference(negated_conjecture,[],[f21])).
% 0.20/0.56  fof(f21,conjecture,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.56  fof(f1323,plain,(
% 0.20/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.20/0.56    inference(forward_demodulation,[],[f1203,f125])).
% 0.20/0.56  fof(f1203,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 0.20/0.56    inference(backward_demodulation,[],[f57,f120])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f119])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f1414,plain,(
% 0.20/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_13)),
% 0.20/0.57    inference(backward_demodulation,[],[f1391,f1408])).
% 0.20/0.57  fof(f1408,plain,(
% 0.20/0.57    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)) ) | (~spl4_5 | ~spl4_7 | ~spl4_13)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1407,f64])).
% 0.20/0.57  fof(f1407,plain,(
% 0.20/0.57    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) | ~r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X2))) ) | (~spl4_5 | ~spl4_7 | ~spl4_13)),
% 0.20/0.57    inference(resolution,[],[f1405,f77])).
% 0.20/0.57  fof(f1405,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl4_5 | ~spl4_7 | ~spl4_13)),
% 0.20/0.57    inference(forward_demodulation,[],[f1404,f357])).
% 0.20/0.57  fof(f357,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(forward_demodulation,[],[f136,f125])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    sK0 = sK2 | ~spl4_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f134])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    spl4_7 <=> sK0 = sK2),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.57  fof(f1404,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k1_xboole_0)) ) | (~spl4_5 | ~spl4_13)),
% 0.20/0.57    inference(forward_demodulation,[],[f185,f125])).
% 0.20/0.57  fof(f185,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK0)) ) | ~spl4_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f184])).
% 0.20/0.57  fof(f184,plain,(
% 0.20/0.57    spl4_13 <=> ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.57  fof(f1391,plain,(
% 0.20/0.57    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(forward_demodulation,[],[f1390,f372])).
% 0.20/0.57  fof(f1390,plain,(
% 0.20/0.57    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(forward_demodulation,[],[f337,f357])).
% 0.20/0.57  fof(f337,plain,(
% 0.20/0.57    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.20/0.57    inference(backward_demodulation,[],[f215,f120])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.57    inference(backward_demodulation,[],[f112,f147])).
% 0.20/0.57  fof(f147,plain,(
% 0.20/0.57    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f139,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f58,f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.57  fof(f1384,plain,(
% 0.20/0.57    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1383])).
% 0.20/0.57  fof(f1383,plain,(
% 0.20/0.57    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1382,f375])).
% 0.20/0.57  fof(f375,plain,(
% 0.20/0.57    v1_relat_1(k1_xboole_0) | ~spl4_5),
% 0.20/0.57    inference(backward_demodulation,[],[f143,f372])).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f58,f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f1382,plain,(
% 0.20/0.57    ~v1_relat_1(k1_xboole_0) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(resolution,[],[f1371,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.57  fof(f1371,plain,(
% 0.20/0.57    ~r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(resolution,[],[f1363,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f52])).
% 0.20/0.57  fof(f1363,plain,(
% 0.20/0.57    ~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(forward_demodulation,[],[f1362,f372])).
% 0.20/0.57  fof(f1362,plain,(
% 0.20/0.57    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(forward_demodulation,[],[f1289,f357])).
% 0.20/0.57  fof(f1289,plain,(
% 0.20/0.57    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 0.20/0.57    inference(forward_demodulation,[],[f1252,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f82])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f54])).
% 0.20/0.57  fof(f1252,plain,(
% 0.20/0.57    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl4_3 | ~spl4_4)),
% 0.20/0.57    inference(backward_demodulation,[],[f1065,f120])).
% 0.20/0.57  fof(f1065,plain,(
% 0.20/0.57    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.57    inference(forward_demodulation,[],[f116,f147])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.57  fof(f1201,plain,(
% 0.20/0.57    ~spl4_12 | spl4_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f435,f184,f180])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    spl4_12 <=> v1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.57  fof(f435,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK0) | ~v1_relat_1(sK2)) )),
% 0.20/0.57    inference(resolution,[],[f127,f67])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK0)) )),
% 0.20/0.57    inference(resolution,[],[f59,f92])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(flattening,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    r1_tarski(sK2,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f1196,plain,(
% 0.20/0.57    spl4_26 | spl4_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f475,f119,f322])).
% 0.20/0.57  fof(f322,plain,(
% 0.20/0.57    spl4_26 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.57  fof(f475,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f467,f57])).
% 0.20/0.57  fof(f467,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.57    inference(resolution,[],[f58,f86])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.57  fof(f1174,plain,(
% 0.20/0.57    spl4_3 | ~spl4_26),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1173])).
% 0.20/0.57  fof(f1173,plain,(
% 0.20/0.57    $false | (spl4_3 | ~spl4_26)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1162,f205])).
% 0.20/0.57  fof(f205,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f200,f143])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f153,f68])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.20/0.57  fof(f153,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK3)) | r1_tarski(X0,sK1)) )),
% 0.20/0.57    inference(resolution,[],[f151,f92])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f150,f143])).
% 0.20/0.57  fof(f150,plain,(
% 0.20/0.57    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f141,f70])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    v5_relat_1(sK3,sK1)),
% 0.20/0.57    inference(resolution,[],[f58,f85])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.57  fof(f1162,plain,(
% 0.20/0.57    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_26)),
% 0.20/0.57    inference(resolution,[],[f625,f1065])).
% 0.20/0.57  fof(f625,plain,(
% 0.20/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl4_26),
% 0.20/0.57    inference(subsumption_resolution,[],[f624,f243])).
% 0.20/0.57  fof(f243,plain,(
% 0.20/0.57    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 0.20/0.57    inference(resolution,[],[f218,f83])).
% 0.20/0.57  fof(f218,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f217,f56])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f216,f58])).
% 0.20/0.57  fof(f216,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.57    inference(superposition,[],[f95,f147])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.57  fof(f624,plain,(
% 0.20/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_26),
% 0.20/0.57    inference(subsumption_resolution,[],[f620,f214])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.57    inference(backward_demodulation,[],[f146,f147])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f138,f56])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f58,f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f620,plain,(
% 0.20/0.57    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_26),
% 0.20/0.57    inference(superposition,[],[f74,f612])).
% 0.20/0.57  fof(f612,plain,(
% 0.20/0.57    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_26),
% 0.20/0.57    inference(resolution,[],[f548,f59])).
% 0.20/0.57  fof(f548,plain,(
% 0.20/0.57    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl4_26),
% 0.20/0.57    inference(subsumption_resolution,[],[f543,f143])).
% 0.20/0.57  fof(f543,plain,(
% 0.20/0.57    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_26),
% 0.20/0.57    inference(superposition,[],[f69,f540])).
% 0.20/0.57  fof(f540,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK3) | ~spl4_26),
% 0.20/0.57    inference(forward_demodulation,[],[f142,f324])).
% 0.20/0.57  fof(f324,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_26),
% 0.20/0.57    inference(avatar_component_clause,[],[f322])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f58,f84])).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.57  fof(f1064,plain,(
% 0.20/0.57    spl4_2 | ~spl4_26),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1063])).
% 0.20/0.57  fof(f1063,plain,(
% 0.20/0.57    $false | (spl4_2 | ~spl4_26)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1042,f215])).
% 0.20/0.57  fof(f1042,plain,(
% 0.20/0.57    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_26),
% 0.20/0.57    inference(resolution,[],[f623,f205])).
% 0.20/0.57  fof(f623,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl4_26),
% 0.20/0.57    inference(subsumption_resolution,[],[f622,f243])).
% 0.20/0.57  fof(f622,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_26),
% 0.20/0.57    inference(subsumption_resolution,[],[f619,f214])).
% 0.20/0.57  fof(f619,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_26),
% 0.20/0.57    inference(superposition,[],[f73,f612])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f462,plain,(
% 0.20/0.57    ~spl4_6 | spl4_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f461,f134,f130])).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    spl4_6 <=> r1_tarski(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.57  fof(f461,plain,(
% 0.20/0.57    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.20/0.57    inference(resolution,[],[f59,f77])).
% 0.20/0.57  fof(f400,plain,(
% 0.20/0.57    ~spl4_5 | ~spl4_7 | spl4_12),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f399])).
% 0.20/0.57  fof(f399,plain,(
% 0.20/0.57    $false | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.57    inference(subsumption_resolution,[],[f365,f375])).
% 0.20/0.57  fof(f365,plain,(
% 0.20/0.57    ~v1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.57    inference(backward_demodulation,[],[f182,f357])).
% 0.20/0.57  fof(f182,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl4_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f180])).
% 0.20/0.57  fof(f356,plain,(
% 0.20/0.57    ~spl4_5 | spl4_6),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f355])).
% 0.20/0.57  fof(f355,plain,(
% 0.20/0.57    $false | (~spl4_5 | spl4_6)),
% 0.20/0.57    inference(subsumption_resolution,[],[f353,f64])).
% 0.20/0.57  fof(f353,plain,(
% 0.20/0.57    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 0.20/0.57    inference(backward_demodulation,[],[f132,f125])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK2) | spl4_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f130])).
% 0.20/0.57  fof(f188,plain,(
% 0.20/0.57    spl4_1),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.57  fof(f187,plain,(
% 0.20/0.57    $false | spl4_1),
% 0.20/0.57    inference(resolution,[],[f146,f108])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    ~spl4_4 | spl4_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f60,f123,f119])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f61,f114,f110,f106])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (14887)------------------------------
% 0.20/0.57  % (14887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (14887)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (14887)Memory used [KB]: 11129
% 0.20/0.57  % (14887)Time elapsed: 0.146 s
% 0.20/0.57  % (14887)------------------------------
% 0.20/0.57  % (14887)------------------------------
% 0.20/0.57  % (14879)Success in time 0.217 s
%------------------------------------------------------------------------------
