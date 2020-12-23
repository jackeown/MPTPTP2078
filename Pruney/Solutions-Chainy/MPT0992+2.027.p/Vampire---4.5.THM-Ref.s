%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:13 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 703 expanded)
%              Number of leaves         :   29 ( 185 expanded)
%              Depth                    :   18
%              Number of atoms          :  550 (4051 expanded)
%              Number of equality atoms :  119 ( 989 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f118,f179,f326,f345,f1060,f1156,f1172,f1187,f1248,f1281,f1288,f1295,f1331,f1503])).

fof(f1503,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f1502])).

fof(f1502,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f1497,f1431])).

fof(f1431,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f1414,f338])).

fof(f338,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f337,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f337,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f164,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f164,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_11
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1414,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1345,f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1345,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f53,f112])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43])).

fof(f43,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1497,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f1438,f1484])).

fof(f1484,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f1483,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1483,plain,
    ( r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1482,f338])).

fof(f1482,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1371,f899])).

fof(f899,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f340,f59])).

fof(f340,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f55,f117])).

fof(f55,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f1371,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1362,f90])).

fof(f1362,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f1304,f112])).

fof(f1304,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f1296,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1296,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f107,f138])).

fof(f138,plain,(
    ! [X1] : k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(subsumption_resolution,[],[f131,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f131,plain,(
    ! [X1] :
      ( k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1438,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1437,f338])).

fof(f1437,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f306,f899])).

fof(f306,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f198,f112])).

fof(f198,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f104,f138])).

fof(f104,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1331,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f1330])).

fof(f1330,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1329,f1296])).

fof(f1329,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1328,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1328,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f1327,f198])).

fof(f1327,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f1326])).

fof(f1326,plain,
    ( sK2 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(superposition,[],[f80,f1307])).

fof(f1307,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f1302,f467])).

fof(f467,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_22 ),
    inference(resolution,[],[f403,f55])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f402,f135])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f402,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl4_22 ),
    inference(superposition,[],[f63,f401])).

fof(f401,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f134,f294])).

fof(f294,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f134,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f54,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f1302,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f1296,f76])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f1295,plain,
    ( ~ spl4_22
    | spl4_66 ),
    inference(avatar_contradiction_clause,[],[f1294])).

fof(f1294,plain,
    ( $false
    | ~ spl4_22
    | spl4_66 ),
    inference(subsumption_resolution,[],[f1293,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f1293,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl4_22
    | spl4_66 ),
    inference(forward_demodulation,[],[f1292,f467])).

fof(f1292,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_66 ),
    inference(forward_demodulation,[],[f1182,f138])).

fof(f1182,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_66 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1180,plain,
    ( spl4_66
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f1288,plain,(
    spl4_67 ),
    inference(avatar_contradiction_clause,[],[f1287])).

fof(f1287,plain,
    ( $false
    | spl4_67 ),
    inference(subsumption_resolution,[],[f1286,f216])).

fof(f216,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f215,f210])).

fof(f210,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f201,f75])).

fof(f201,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f200,f52])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f199,f54])).

fof(f199,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f87,f138])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f215,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f208,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f208,plain,(
    ! [X5] : v5_relat_1(k7_relat_1(sK3,X5),sK1) ),
    inference(resolution,[],[f201,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1286,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_67 ),
    inference(forward_demodulation,[],[f1186,f138])).

fof(f1186,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_67 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f1184,plain,
    ( spl4_67
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1281,plain,(
    spl4_65 ),
    inference(avatar_contradiction_clause,[],[f1280])).

fof(f1280,plain,
    ( $false
    | spl4_65 ),
    inference(subsumption_resolution,[],[f1275,f210])).

fof(f1275,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_65 ),
    inference(backward_demodulation,[],[f1178,f138])).

fof(f1178,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1176,plain,
    ( spl4_65
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1248,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f1247,f162,f158])).

fof(f158,plain,
    ( spl4_10
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1247,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f136,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f136,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f54,f69])).

fof(f1187,plain,
    ( ~ spl4_65
    | ~ spl4_66
    | ~ spl4_67
    | spl4_3 ),
    inference(avatar_split_clause,[],[f1173,f106,f1184,f1180,f1176])).

fof(f1173,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_3 ),
    inference(resolution,[],[f108,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f108,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1172,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f1171,f126,f122])).

fof(f122,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1171,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f55,f68])).

fof(f1156,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1155])).

fof(f1155,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1154,f52])).

fof(f1154,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1151,f54])).

fof(f1151,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f1143,f87])).

fof(f1143,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f108,f128])).

fof(f128,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1060,plain,
    ( spl4_22
    | spl4_4 ),
    inference(avatar_split_clause,[],[f955,f111,f292])).

fof(f955,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f948,f53])).

fof(f948,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f345,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f342,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f124,f117])).

fof(f124,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f326,plain,
    ( ~ spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f324,f58])).

fof(f324,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_4
    | spl4_10 ),
    inference(forward_demodulation,[],[f305,f90])).

fof(f305,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | ~ spl4_4
    | spl4_10 ),
    inference(backward_demodulation,[],[f160,f112])).

fof(f160,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f179,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f137,f100])).

fof(f100,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f137,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f130,f52])).

fof(f130,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f54,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f56,f115,f111])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f106,f102,f98])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:17:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.45  % (20931)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.46  % (20946)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.18/0.46  % (20929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.46  % (20948)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.47  % (20940)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.47  % (20938)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.18/0.48  % (20930)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.49  % (20944)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.18/0.49  % (20945)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.18/0.49  % (20925)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.49  % (20936)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.18/0.49  % (20937)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.18/0.49  % (20947)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.49  % (20928)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.49  % (20939)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.18/0.50  % (20949)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.18/0.50  % (20941)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.18/0.51  % (20935)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.18/0.51  % (20927)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (20933)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.18/0.51  % (20942)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.18/0.51  % (20932)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.18/0.52  % (20934)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.18/0.52  % (20943)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.18/0.53  % (20951)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.18/0.54  % (20950)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.92/0.61  % (20927)Refutation found. Thanks to Tanya!
% 1.92/0.61  % SZS status Theorem for theBenchmark
% 1.92/0.61  % SZS output start Proof for theBenchmark
% 1.92/0.61  fof(f1504,plain,(
% 1.92/0.61    $false),
% 1.92/0.61    inference(avatar_sat_refutation,[],[f109,f118,f179,f326,f345,f1060,f1156,f1172,f1187,f1248,f1281,f1288,f1295,f1331,f1503])).
% 1.92/0.61  fof(f1503,plain,(
% 1.92/0.61    spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1502])).
% 1.92/0.61  fof(f1502,plain,(
% 1.92/0.61    $false | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1497,f1431])).
% 1.92/0.61  fof(f1431,plain,(
% 1.92/0.61    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(backward_demodulation,[],[f1414,f338])).
% 1.92/0.61  fof(f338,plain,(
% 1.92/0.61    k1_xboole_0 = sK3 | (~spl4_4 | ~spl4_11)),
% 1.92/0.61    inference(forward_demodulation,[],[f337,f90])).
% 1.92/0.61  fof(f90,plain,(
% 1.92/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.92/0.61    inference(equality_resolution,[],[f73])).
% 1.92/0.61  fof(f73,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.92/0.61    inference(cnf_transformation,[],[f50])).
% 1.92/0.61  fof(f50,plain,(
% 1.92/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.92/0.61    inference(flattening,[],[f49])).
% 1.92/0.61  fof(f49,plain,(
% 1.92/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.92/0.61    inference(nnf_transformation,[],[f5])).
% 1.92/0.61  fof(f5,axiom,(
% 1.92/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.92/0.61  fof(f337,plain,(
% 1.92/0.61    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 1.92/0.61    inference(forward_demodulation,[],[f164,f112])).
% 1.92/0.61  fof(f112,plain,(
% 1.92/0.61    k1_xboole_0 = sK1 | ~spl4_4),
% 1.92/0.61    inference(avatar_component_clause,[],[f111])).
% 1.92/0.61  fof(f111,plain,(
% 1.92/0.61    spl4_4 <=> k1_xboole_0 = sK1),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.92/0.61  fof(f164,plain,(
% 1.92/0.61    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl4_11),
% 1.92/0.61    inference(avatar_component_clause,[],[f162])).
% 1.92/0.61  fof(f162,plain,(
% 1.92/0.61    spl4_11 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.92/0.61  fof(f1414,plain,(
% 1.92/0.61    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.92/0.61    inference(forward_demodulation,[],[f1345,f117])).
% 1.92/0.61  fof(f117,plain,(
% 1.92/0.61    k1_xboole_0 = sK0 | ~spl4_5),
% 1.92/0.61    inference(avatar_component_clause,[],[f115])).
% 1.92/0.61  fof(f115,plain,(
% 1.92/0.61    spl4_5 <=> k1_xboole_0 = sK0),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.92/0.61  fof(f1345,plain,(
% 1.92/0.61    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.92/0.61    inference(backward_demodulation,[],[f53,f112])).
% 1.92/0.61  fof(f53,plain,(
% 1.92/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  fof(f44,plain,(
% 1.92/0.61    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.92/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43])).
% 1.92/0.61  fof(f43,plain,(
% 1.92/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.92/0.61    introduced(choice_axiom,[])).
% 1.92/0.61  fof(f23,plain,(
% 1.92/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.92/0.61    inference(flattening,[],[f22])).
% 1.92/0.61  fof(f22,plain,(
% 1.92/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.92/0.61    inference(ennf_transformation,[],[f20])).
% 1.92/0.61  fof(f20,negated_conjecture,(
% 1.92/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.92/0.61    inference(negated_conjecture,[],[f19])).
% 1.92/0.61  fof(f19,conjecture,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.92/0.61  fof(f1497,plain,(
% 1.92/0.61    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(backward_demodulation,[],[f1438,f1484])).
% 1.92/0.61  fof(f1484,plain,(
% 1.92/0.61    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(resolution,[],[f1483,f59])).
% 1.92/0.61  fof(f59,plain,(
% 1.92/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f24])).
% 1.92/0.61  fof(f24,plain,(
% 1.92/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.92/0.61    inference(ennf_transformation,[],[f4])).
% 1.92/0.61  fof(f4,axiom,(
% 1.92/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.92/0.61  fof(f1483,plain,(
% 1.92/0.61    r1_tarski(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(forward_demodulation,[],[f1482,f338])).
% 1.92/0.61  fof(f1482,plain,(
% 1.92/0.61    r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.92/0.61    inference(forward_demodulation,[],[f1371,f899])).
% 1.92/0.61  fof(f899,plain,(
% 1.92/0.61    k1_xboole_0 = sK2 | ~spl4_5),
% 1.92/0.61    inference(resolution,[],[f340,f59])).
% 1.92/0.61  fof(f340,plain,(
% 1.92/0.61    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.92/0.61    inference(backward_demodulation,[],[f55,f117])).
% 1.92/0.61  fof(f55,plain,(
% 1.92/0.61    r1_tarski(sK2,sK0)),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  fof(f1371,plain,(
% 1.92/0.61    r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) | (~spl4_3 | ~spl4_4)),
% 1.92/0.61    inference(forward_demodulation,[],[f1362,f90])).
% 1.92/0.61  fof(f1362,plain,(
% 1.92/0.61    r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,k1_xboole_0)) | (~spl4_3 | ~spl4_4)),
% 1.92/0.61    inference(backward_demodulation,[],[f1304,f112])).
% 1.92/0.61  fof(f1304,plain,(
% 1.92/0.61    r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) | ~spl4_3),
% 1.92/0.61    inference(resolution,[],[f1296,f69])).
% 1.92/0.61  fof(f69,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f48])).
% 1.92/0.61  fof(f48,plain,(
% 1.92/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.92/0.61    inference(nnf_transformation,[],[f6])).
% 1.92/0.61  fof(f6,axiom,(
% 1.92/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.92/0.61  fof(f1296,plain,(
% 1.92/0.61    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.92/0.61    inference(forward_demodulation,[],[f107,f138])).
% 1.92/0.61  fof(f138,plain,(
% 1.92/0.61    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f131,f52])).
% 1.92/0.61  fof(f52,plain,(
% 1.92/0.61    v1_funct_1(sK3)),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  fof(f131,plain,(
% 1.92/0.61    ( ! [X1] : (k2_partfun1(sK0,sK1,sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.92/0.61    inference(resolution,[],[f54,f85])).
% 1.92/0.61  fof(f85,plain,(
% 1.92/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f40])).
% 1.92/0.61  fof(f40,plain,(
% 1.92/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.92/0.61    inference(flattening,[],[f39])).
% 1.92/0.61  fof(f39,plain,(
% 1.92/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.92/0.61    inference(ennf_transformation,[],[f18])).
% 1.92/0.61  fof(f18,axiom,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.92/0.61  fof(f54,plain,(
% 1.92/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  fof(f107,plain,(
% 1.92/0.61    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.92/0.61    inference(avatar_component_clause,[],[f106])).
% 1.92/0.61  fof(f106,plain,(
% 1.92/0.61    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.92/0.61  fof(f1438,plain,(
% 1.92/0.61    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_11)),
% 1.92/0.61    inference(forward_demodulation,[],[f1437,f338])).
% 1.92/0.61  fof(f1437,plain,(
% 1.92/0.61    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.92/0.61    inference(forward_demodulation,[],[f306,f899])).
% 1.92/0.61  fof(f306,plain,(
% 1.92/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.92/0.61    inference(backward_demodulation,[],[f198,f112])).
% 1.92/0.61  fof(f198,plain,(
% 1.92/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.92/0.61    inference(backward_demodulation,[],[f104,f138])).
% 1.92/0.61  fof(f104,plain,(
% 1.92/0.61    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.92/0.61    inference(avatar_component_clause,[],[f102])).
% 1.92/0.61  fof(f102,plain,(
% 1.92/0.61    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.92/0.61  fof(f1331,plain,(
% 1.92/0.61    spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1330])).
% 1.92/0.61  fof(f1330,plain,(
% 1.92/0.61    $false | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1329,f1296])).
% 1.92/0.61  fof(f1329,plain,(
% 1.92/0.61    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4 | ~spl4_22)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1328,f113])).
% 1.92/0.61  fof(f113,plain,(
% 1.92/0.61    k1_xboole_0 != sK1 | spl4_4),
% 1.92/0.61    inference(avatar_component_clause,[],[f111])).
% 1.92/0.61  fof(f1328,plain,(
% 1.92/0.61    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | ~spl4_22)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1327,f198])).
% 1.92/0.61  fof(f1327,plain,(
% 1.92/0.61    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_22)),
% 1.92/0.61    inference(trivial_inequality_removal,[],[f1326])).
% 1.92/0.61  fof(f1326,plain,(
% 1.92/0.61    sK2 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_3 | ~spl4_22)),
% 1.92/0.61    inference(superposition,[],[f80,f1307])).
% 1.92/0.61  fof(f1307,plain,(
% 1.92/0.61    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_22)),
% 1.92/0.61    inference(forward_demodulation,[],[f1302,f467])).
% 1.92/0.61  fof(f467,plain,(
% 1.92/0.61    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_22),
% 1.92/0.61    inference(resolution,[],[f403,f55])).
% 1.92/0.61  fof(f403,plain,(
% 1.92/0.61    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_22),
% 1.92/0.61    inference(subsumption_resolution,[],[f402,f135])).
% 1.92/0.61  fof(f135,plain,(
% 1.92/0.61    v1_relat_1(sK3)),
% 1.92/0.61    inference(resolution,[],[f54,f75])).
% 1.92/0.61  fof(f75,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f32])).
% 1.92/0.61  fof(f32,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(ennf_transformation,[],[f12])).
% 1.92/0.61  fof(f12,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.92/0.61  fof(f402,plain,(
% 1.92/0.61    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl4_22),
% 1.92/0.61    inference(superposition,[],[f63,f401])).
% 1.92/0.61  fof(f401,plain,(
% 1.92/0.61    sK0 = k1_relat_1(sK3) | ~spl4_22),
% 1.92/0.61    inference(forward_demodulation,[],[f134,f294])).
% 1.92/0.61  fof(f294,plain,(
% 1.92/0.61    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_22),
% 1.92/0.61    inference(avatar_component_clause,[],[f292])).
% 1.92/0.61  fof(f292,plain,(
% 1.92/0.61    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.92/0.61  fof(f134,plain,(
% 1.92/0.61    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.92/0.61    inference(resolution,[],[f54,f76])).
% 1.92/0.61  fof(f76,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f33])).
% 1.92/0.61  fof(f33,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(ennf_transformation,[],[f14])).
% 1.92/0.61  fof(f14,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.92/0.61  fof(f63,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f28])).
% 1.92/0.61  fof(f28,plain,(
% 1.92/0.61    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.92/0.61    inference(flattening,[],[f27])).
% 1.92/0.61  fof(f27,plain,(
% 1.92/0.61    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.92/0.61    inference(ennf_transformation,[],[f11])).
% 1.92/0.61  fof(f11,axiom,(
% 1.92/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.92/0.61  fof(f1302,plain,(
% 1.92/0.61    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_3),
% 1.92/0.61    inference(resolution,[],[f1296,f76])).
% 1.92/0.61  fof(f80,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f51])).
% 1.92/0.61  fof(f51,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(nnf_transformation,[],[f36])).
% 1.92/0.61  fof(f36,plain,(
% 1.92/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(flattening,[],[f35])).
% 1.92/0.61  fof(f35,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(ennf_transformation,[],[f16])).
% 1.92/0.61  fof(f16,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.92/0.61  fof(f1295,plain,(
% 1.92/0.61    ~spl4_22 | spl4_66),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1294])).
% 1.92/0.61  fof(f1294,plain,(
% 1.92/0.61    $false | (~spl4_22 | spl4_66)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1293,f89])).
% 1.92/0.61  fof(f89,plain,(
% 1.92/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.92/0.61    inference(equality_resolution,[],[f66])).
% 1.92/0.61  fof(f66,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.92/0.61    inference(cnf_transformation,[],[f47])).
% 1.92/0.61  fof(f47,plain,(
% 1.92/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.61    inference(flattening,[],[f46])).
% 1.92/0.61  fof(f46,plain,(
% 1.92/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.61    inference(nnf_transformation,[],[f1])).
% 1.92/0.61  fof(f1,axiom,(
% 1.92/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.92/0.61  fof(f1293,plain,(
% 1.92/0.61    ~r1_tarski(sK2,sK2) | (~spl4_22 | spl4_66)),
% 1.92/0.61    inference(forward_demodulation,[],[f1292,f467])).
% 1.92/0.61  fof(f1292,plain,(
% 1.92/0.61    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_66),
% 1.92/0.61    inference(forward_demodulation,[],[f1182,f138])).
% 1.92/0.61  fof(f1182,plain,(
% 1.92/0.61    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_66),
% 1.92/0.61    inference(avatar_component_clause,[],[f1180])).
% 1.92/0.61  fof(f1180,plain,(
% 1.92/0.61    spl4_66 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.92/0.61  fof(f1288,plain,(
% 1.92/0.61    spl4_67),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1287])).
% 1.92/0.61  fof(f1287,plain,(
% 1.92/0.61    $false | spl4_67),
% 1.92/0.61    inference(subsumption_resolution,[],[f1286,f216])).
% 1.92/0.61  fof(f216,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f215,f210])).
% 1.92/0.61  fof(f210,plain,(
% 1.92/0.61    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 1.92/0.61    inference(resolution,[],[f201,f75])).
% 1.92/0.61  fof(f201,plain,(
% 1.92/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f200,f52])).
% 1.92/0.61  fof(f200,plain,(
% 1.92/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f199,f54])).
% 1.92/0.61  fof(f199,plain,(
% 1.92/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.92/0.61    inference(superposition,[],[f87,f138])).
% 1.92/0.61  fof(f87,plain,(
% 1.92/0.61    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f42])).
% 1.92/0.61  fof(f42,plain,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.92/0.61    inference(flattening,[],[f41])).
% 1.92/0.61  fof(f41,plain,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.92/0.61    inference(ennf_transformation,[],[f17])).
% 1.92/0.61  fof(f17,axiom,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.92/0.61  fof(f215,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.92/0.61    inference(resolution,[],[f208,f64])).
% 1.92/0.61  fof(f64,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f45])).
% 1.92/0.61  fof(f45,plain,(
% 1.92/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.92/0.61    inference(nnf_transformation,[],[f29])).
% 1.92/0.61  fof(f29,plain,(
% 1.92/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.92/0.61    inference(ennf_transformation,[],[f7])).
% 1.92/0.61  fof(f7,axiom,(
% 1.92/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.92/0.61  fof(f208,plain,(
% 1.92/0.61    ( ! [X5] : (v5_relat_1(k7_relat_1(sK3,X5),sK1)) )),
% 1.92/0.61    inference(resolution,[],[f201,f77])).
% 1.92/0.61  fof(f77,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f34])).
% 1.92/0.61  fof(f34,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.61    inference(ennf_transformation,[],[f21])).
% 1.92/0.61  fof(f21,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.92/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.92/0.61  fof(f13,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.92/0.61  fof(f1286,plain,(
% 1.92/0.61    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_67),
% 1.92/0.61    inference(forward_demodulation,[],[f1186,f138])).
% 1.92/0.61  fof(f1186,plain,(
% 1.92/0.61    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_67),
% 1.92/0.61    inference(avatar_component_clause,[],[f1184])).
% 1.92/0.61  fof(f1184,plain,(
% 1.92/0.61    spl4_67 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.92/0.61  fof(f1281,plain,(
% 1.92/0.61    spl4_65),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1280])).
% 1.92/0.61  fof(f1280,plain,(
% 1.92/0.61    $false | spl4_65),
% 1.92/0.61    inference(subsumption_resolution,[],[f1275,f210])).
% 1.92/0.61  fof(f1275,plain,(
% 1.92/0.61    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_65),
% 1.92/0.61    inference(backward_demodulation,[],[f1178,f138])).
% 1.92/0.61  fof(f1178,plain,(
% 1.92/0.61    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_65),
% 1.92/0.61    inference(avatar_component_clause,[],[f1176])).
% 1.92/0.61  fof(f1176,plain,(
% 1.92/0.61    spl4_65 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.92/0.61  fof(f1248,plain,(
% 1.92/0.61    ~spl4_10 | spl4_11),
% 1.92/0.61    inference(avatar_split_clause,[],[f1247,f162,f158])).
% 1.92/0.61  fof(f158,plain,(
% 1.92/0.61    spl4_10 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.92/0.61  fof(f1247,plain,(
% 1.92/0.61    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.92/0.61    inference(resolution,[],[f136,f68])).
% 1.92/0.61  fof(f68,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f47])).
% 1.92/0.61  fof(f136,plain,(
% 1.92/0.61    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.92/0.61    inference(resolution,[],[f54,f69])).
% 1.92/0.61  fof(f1187,plain,(
% 1.92/0.61    ~spl4_65 | ~spl4_66 | ~spl4_67 | spl4_3),
% 1.92/0.61    inference(avatar_split_clause,[],[f1173,f106,f1184,f1180,f1176])).
% 1.92/0.61  fof(f1173,plain,(
% 1.92/0.61    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_3),
% 1.92/0.61    inference(resolution,[],[f108,f74])).
% 1.92/0.61  fof(f74,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f31])).
% 1.92/0.61  fof(f31,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.92/0.61    inference(flattening,[],[f30])).
% 1.92/0.61  fof(f30,plain,(
% 1.92/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.92/0.61    inference(ennf_transformation,[],[f15])).
% 1.92/0.61  fof(f15,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.92/0.61  fof(f108,plain,(
% 1.92/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.92/0.61    inference(avatar_component_clause,[],[f106])).
% 1.92/0.61  fof(f1172,plain,(
% 1.92/0.61    ~spl4_6 | spl4_7),
% 1.92/0.61    inference(avatar_split_clause,[],[f1171,f126,f122])).
% 1.92/0.61  fof(f122,plain,(
% 1.92/0.61    spl4_6 <=> r1_tarski(sK0,sK2)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.92/0.61  fof(f126,plain,(
% 1.92/0.61    spl4_7 <=> sK0 = sK2),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.92/0.61  fof(f1171,plain,(
% 1.92/0.61    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.92/0.61    inference(resolution,[],[f55,f68])).
% 1.92/0.61  fof(f1156,plain,(
% 1.92/0.61    spl4_3 | ~spl4_7),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1155])).
% 1.92/0.61  fof(f1155,plain,(
% 1.92/0.61    $false | (spl4_3 | ~spl4_7)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1154,f52])).
% 1.92/0.61  fof(f1154,plain,(
% 1.92/0.61    ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1151,f54])).
% 1.92/0.61  fof(f1151,plain,(
% 1.92/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7)),
% 1.92/0.61    inference(resolution,[],[f1143,f87])).
% 1.92/0.61  fof(f1143,plain,(
% 1.92/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 1.92/0.61    inference(forward_demodulation,[],[f108,f128])).
% 1.92/0.61  fof(f128,plain,(
% 1.92/0.61    sK0 = sK2 | ~spl4_7),
% 1.92/0.61    inference(avatar_component_clause,[],[f126])).
% 1.92/0.61  fof(f1060,plain,(
% 1.92/0.61    spl4_22 | spl4_4),
% 1.92/0.61    inference(avatar_split_clause,[],[f955,f111,f292])).
% 1.92/0.61  fof(f955,plain,(
% 1.92/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.92/0.61    inference(subsumption_resolution,[],[f948,f53])).
% 1.92/0.61  fof(f948,plain,(
% 1.92/0.61    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.92/0.61    inference(resolution,[],[f54,f78])).
% 1.92/0.61  fof(f78,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f51])).
% 1.92/0.61  fof(f345,plain,(
% 1.92/0.61    ~spl4_5 | spl4_6),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f344])).
% 1.92/0.61  fof(f344,plain,(
% 1.92/0.61    $false | (~spl4_5 | spl4_6)),
% 1.92/0.61    inference(subsumption_resolution,[],[f342,f58])).
% 1.92/0.61  fof(f58,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f3])).
% 1.92/0.61  fof(f3,axiom,(
% 1.92/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.92/0.61  fof(f342,plain,(
% 1.92/0.61    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 1.92/0.61    inference(backward_demodulation,[],[f124,f117])).
% 1.92/0.61  fof(f124,plain,(
% 1.92/0.61    ~r1_tarski(sK0,sK2) | spl4_6),
% 1.92/0.61    inference(avatar_component_clause,[],[f122])).
% 1.92/0.61  fof(f326,plain,(
% 1.92/0.61    ~spl4_4 | spl4_10),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f325])).
% 1.92/0.61  fof(f325,plain,(
% 1.92/0.61    $false | (~spl4_4 | spl4_10)),
% 1.92/0.61    inference(subsumption_resolution,[],[f324,f58])).
% 1.92/0.61  fof(f324,plain,(
% 1.92/0.61    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_4 | spl4_10)),
% 1.92/0.61    inference(forward_demodulation,[],[f305,f90])).
% 1.92/0.61  fof(f305,plain,(
% 1.92/0.61    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (~spl4_4 | spl4_10)),
% 1.92/0.61    inference(backward_demodulation,[],[f160,f112])).
% 1.92/0.61  fof(f160,plain,(
% 1.92/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl4_10),
% 1.92/0.61    inference(avatar_component_clause,[],[f158])).
% 1.92/0.61  fof(f179,plain,(
% 1.92/0.61    spl4_1),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f178])).
% 1.92/0.61  fof(f178,plain,(
% 1.92/0.61    $false | spl4_1),
% 1.92/0.61    inference(resolution,[],[f137,f100])).
% 1.92/0.61  fof(f100,plain,(
% 1.92/0.61    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.92/0.61    inference(avatar_component_clause,[],[f98])).
% 1.92/0.61  fof(f98,plain,(
% 1.92/0.61    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.92/0.61  fof(f137,plain,(
% 1.92/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f130,f52])).
% 1.92/0.61  fof(f130,plain,(
% 1.92/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.92/0.61    inference(resolution,[],[f54,f86])).
% 1.92/0.61  fof(f86,plain,(
% 1.92/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f42])).
% 1.92/0.61  fof(f118,plain,(
% 1.92/0.61    ~spl4_4 | spl4_5),
% 1.92/0.61    inference(avatar_split_clause,[],[f56,f115,f111])).
% 1.92/0.61  fof(f56,plain,(
% 1.92/0.61    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  fof(f109,plain,(
% 1.92/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.92/0.61    inference(avatar_split_clause,[],[f57,f106,f102,f98])).
% 1.92/0.61  fof(f57,plain,(
% 1.92/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.92/0.61    inference(cnf_transformation,[],[f44])).
% 1.92/0.61  % SZS output end Proof for theBenchmark
% 1.92/0.61  % (20927)------------------------------
% 1.92/0.61  % (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.61  % (20927)Termination reason: Refutation
% 1.92/0.61  
% 1.92/0.61  % (20927)Memory used [KB]: 11257
% 1.92/0.61  % (20927)Time elapsed: 0.216 s
% 1.92/0.61  % (20927)------------------------------
% 1.92/0.61  % (20927)------------------------------
% 1.92/0.61  % (20922)Success in time 0.274 s
%------------------------------------------------------------------------------
