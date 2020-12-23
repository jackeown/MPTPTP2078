%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:57 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  120 (1173 expanded)
%              Number of leaves         :   22 ( 260 expanded)
%              Depth                    :   16
%              Number of atoms          :  306 (3385 expanded)
%              Number of equality atoms :   40 ( 197 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1083,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f414,f583,f975,f980,f989,f1081])).

fof(f1081,plain,
    ( ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f462,f87,f1011,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f1011,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f906,f994])).

fof(f994,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f966,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f966,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f964])).

fof(f964,plain,
    ( spl8_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f906,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f441,f898])).

fof(f898,plain,
    ( k1_xboole_0 = sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f57,f459,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f459,plain,
    ( r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f404,f421])).

fof(f421,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f420,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f420,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f142,f313])).

fof(f313,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f231,f232,f123,f233,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f233,plain,(
    m1_subset_1(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f34,f35,f122,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f122,plain,(
    r2_hidden(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f123,plain,(
    ~ r2_hidden(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f232,plain,(
    v1_funct_2(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f35,f122,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f231,plain,(
    v1_funct_1(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f34,f35,f122,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f142,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_1
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f404,plain,(
    r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f369,f90])).

fof(f369,plain,(
    r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f315,f313])).

fof(f315,plain,(
    r1_tarski(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f233,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f441,plain,
    ( ~ r2_hidden(sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f321,f421])).

fof(f321,plain,(
    ~ r2_hidden(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f123,f313])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f462,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f461,f72])).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f461,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f424,f73])).

fof(f73,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f424,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f97,f421])).

fof(f97,plain,(
    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f34,f87,f93,f80])).

fof(f80,plain,(
    ! [X4,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,k1_funct_2(k1_relat_1(X4),X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,X2)
      | k1_funct_2(k1_relat_1(X4),X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | k1_relat_1(X4) != X0
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | X3 != X4
      | k1_relat_1(X4) != X0
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f69,f35,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f989,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f57,f974,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f974,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl8_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f980,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f976])).

fof(f976,plain,
    ( $false
    | ~ spl8_1
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f422,f970])).

fof(f970,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl8_8
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f422,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f34,f421])).

fof(f975,plain,
    ( spl8_7
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f502,f140,f972,f968,f572,f964])).

fof(f572,plain,
    ( spl8_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f502,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f460,f421])).

fof(f460,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f417,f421])).

fof(f417,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f416,f90])).

fof(f416,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f347,f313])).

fof(f347,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK0) ),
    inference(backward_demodulation,[],[f246,f313])).

fof(f246,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f234,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f234,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f583,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f77,f574])).

fof(f574,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f572])).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f414,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f77,f377])).

fof(f377,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_2 ),
    inference(forward_demodulation,[],[f328,f90])).

fof(f328,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl8_2 ),
    inference(backward_demodulation,[],[f183,f313])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f166,f75])).

fof(f166,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f146,f52])).

fof(f146,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f147,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f99,f144,f140])).

fof(f99,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f94,f56])).

fof(f94,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16174)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (16166)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (16184)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (16175)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16167)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16172)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (16185)Refutation not found, incomplete strategy% (16185)------------------------------
% 0.21/0.53  % (16185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16185)Memory used [KB]: 10874
% 0.21/0.53  % (16185)Time elapsed: 0.071 s
% 0.21/0.53  % (16185)------------------------------
% 0.21/0.53  % (16185)------------------------------
% 0.21/0.53  % (16161)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (16171)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (16162)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (16173)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (16182)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (16165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (16186)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (16187)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (16176)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (16191)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (16163)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (16177)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (16181)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (16168)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (16183)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (16190)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (16164)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.56  % (16188)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (16170)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (16169)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (16178)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  % (16189)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.57  % (16165)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f1083,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f147,f414,f583,f975,f980,f989,f1081])).
% 1.56/0.57  fof(f1081,plain,(
% 1.56/0.57    ~spl8_1 | ~spl8_7),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f1069])).
% 1.56/0.57  fof(f1069,plain,(
% 1.56/0.57    $false | (~spl8_1 | ~spl8_7)),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f462,f87,f1011,f51])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f23])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.57    inference(ennf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.57  fof(f1011,plain,(
% 1.56/0.57    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl8_1 | ~spl8_7)),
% 1.56/0.57    inference(backward_demodulation,[],[f906,f994])).
% 1.56/0.57  fof(f994,plain,(
% 1.56/0.57    k1_xboole_0 = sK0 | ~spl8_7),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f966,f76])).
% 1.56/0.57  fof(f76,plain,(
% 1.56/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.56/0.57  fof(f966,plain,(
% 1.56/0.57    v1_xboole_0(sK0) | ~spl8_7),
% 1.56/0.57    inference(avatar_component_clause,[],[f964])).
% 1.56/0.57  fof(f964,plain,(
% 1.56/0.57    spl8_7 <=> v1_xboole_0(sK0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.56/0.57  fof(f906,plain,(
% 1.56/0.57    ~r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0)) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f441,f898])).
% 1.56/0.57  fof(f898,plain,(
% 1.56/0.57    k1_xboole_0 = sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)) | ~spl8_1),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f57,f459,f56])).
% 1.56/0.57  fof(f56,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.57  fof(f459,plain,(
% 1.56/0.57    r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f404,f421])).
% 1.56/0.57  fof(f421,plain,(
% 1.56/0.57    k1_xboole_0 = sK2 | ~spl8_1),
% 1.56/0.57    inference(forward_demodulation,[],[f420,f90])).
% 1.56/0.57  fof(f90,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.56/0.57    inference(equality_resolution,[],[f68])).
% 1.56/0.57  fof(f68,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.56/0.57  fof(f420,plain,(
% 1.56/0.57    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~spl8_1),
% 1.56/0.57    inference(forward_demodulation,[],[f142,f313])).
% 1.56/0.57  fof(f313,plain,(
% 1.56/0.57    k1_xboole_0 = sK1),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f231,f232,f123,f233,f58])).
% 1.56/0.57  fof(f58,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.56/0.57    inference(flattening,[],[f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.56/0.57    inference(ennf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 1.56/0.57  fof(f233,plain,(
% 1.56/0.57    m1_subset_1(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f34,f35,f122,f62])).
% 1.56/0.57  fof(f62,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.56/0.57    inference(flattening,[],[f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.56/0.57    inference(ennf_transformation,[],[f18])).
% 1.56/0.57  fof(f18,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.56/0.57  fof(f122,plain,(
% 1.56/0.57    r2_hidden(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f36,f52])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f23])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.56/0.57    inference(cnf_transformation,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.56/0.57    inference(flattening,[],[f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.56/0.57    inference(ennf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.56/0.57    inference(negated_conjecture,[],[f19])).
% 1.56/0.57  fof(f19,conjecture,(
% 1.56/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.57    inference(cnf_transformation,[],[f22])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    v1_funct_1(sK2)),
% 1.56/0.57    inference(cnf_transformation,[],[f22])).
% 1.56/0.57  fof(f123,plain,(
% 1.56/0.57    ~r2_hidden(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f36,f53])).
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f23])).
% 1.56/0.57  fof(f232,plain,(
% 1.56/0.57    v1_funct_2(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f34,f35,f122,f61])).
% 1.56/0.57  fof(f61,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_2(X3,X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f231,plain,(
% 1.56/0.57    v1_funct_1(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f34,f35,f122,f60])).
% 1.56/0.57  fof(f60,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(X3)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f142,plain,(
% 1.56/0.57    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl8_1),
% 1.56/0.57    inference(avatar_component_clause,[],[f140])).
% 1.56/0.57  fof(f140,plain,(
% 1.56/0.57    spl8_1 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.56/0.57  fof(f404,plain,(
% 1.56/0.57    r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.56/0.57    inference(forward_demodulation,[],[f369,f90])).
% 1.56/0.57  fof(f369,plain,(
% 1.56/0.57    r1_tarski(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.56/0.57    inference(backward_demodulation,[],[f315,f313])).
% 1.56/0.57  fof(f315,plain,(
% 1.56/0.57    r1_tarski(sK6(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f233,f50])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.57  fof(f57,plain,(
% 1.56/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.57  fof(f441,plain,(
% 1.56/0.57    ~r2_hidden(sK6(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f321,f421])).
% 1.56/0.57  fof(f321,plain,(
% 1.56/0.57    ~r2_hidden(sK6(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 1.56/0.57    inference(backward_demodulation,[],[f123,f313])).
% 1.56/0.57  fof(f87,plain,(
% 1.56/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.57    inference(equality_resolution,[],[f55])).
% 1.56/0.57  fof(f55,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f462,plain,(
% 1.56/0.57    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl8_1),
% 1.56/0.57    inference(forward_demodulation,[],[f461,f72])).
% 1.56/0.57  fof(f72,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,axiom,(
% 1.56/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.56/0.57  fof(f461,plain,(
% 1.56/0.57    r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl8_1),
% 1.56/0.57    inference(forward_demodulation,[],[f424,f73])).
% 1.56/0.57  fof(f73,plain,(
% 1.56/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f424,plain,(
% 1.56/0.57    r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f97,f421])).
% 1.56/0.57  fof(f97,plain,(
% 1.56/0.57    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f34,f87,f93,f80])).
% 1.56/0.57  fof(f80,plain,(
% 1.56/0.57    ( ! [X4,X1] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,k1_funct_2(k1_relat_1(X4),X1))) )),
% 1.56/0.57    inference(equality_resolution,[],[f79])).
% 1.56/0.57  fof(f79,plain,(
% 1.56/0.57    ( ! [X4,X2,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,X2) | k1_funct_2(k1_relat_1(X4),X1) != X2) )),
% 1.56/0.57    inference(equality_resolution,[],[f78])).
% 1.56/0.57  fof(f78,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | k1_relat_1(X4) != X0 | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.56/0.57    inference(equality_resolution,[],[f48])).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | X3 != X4 | k1_relat_1(X4) != X0 | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.56/0.57    inference(cnf_transformation,[],[f14])).
% 1.56/0.57  fof(f14,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 1.56/0.57  fof(f93,plain,(
% 1.56/0.57    v1_relat_1(sK2)),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f69,f35,f65])).
% 1.56/0.57  fof(f65,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.56/0.57  fof(f69,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.57  fof(f989,plain,(
% 1.56/0.57    spl8_9),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f984])).
% 1.56/0.57  fof(f984,plain,(
% 1.56/0.57    $false | spl8_9),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f57,f974,f49])).
% 1.56/0.57  fof(f49,plain,(
% 1.56/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f974,plain,(
% 1.56/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl8_9),
% 1.56/0.57    inference(avatar_component_clause,[],[f972])).
% 1.56/0.57  fof(f972,plain,(
% 1.56/0.57    spl8_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.56/0.57  fof(f980,plain,(
% 1.56/0.57    ~spl8_1 | spl8_8),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f976])).
% 1.56/0.57  fof(f976,plain,(
% 1.56/0.57    $false | (~spl8_1 | spl8_8)),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f422,f970])).
% 1.56/0.57  fof(f970,plain,(
% 1.56/0.57    ~v1_funct_1(k1_xboole_0) | spl8_8),
% 1.56/0.57    inference(avatar_component_clause,[],[f968])).
% 1.56/0.57  fof(f968,plain,(
% 1.56/0.57    spl8_8 <=> v1_funct_1(k1_xboole_0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.56/0.57  fof(f422,plain,(
% 1.56/0.57    v1_funct_1(k1_xboole_0) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f34,f421])).
% 1.56/0.57  fof(f975,plain,(
% 1.56/0.57    spl8_7 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_1),
% 1.56/0.57    inference(avatar_split_clause,[],[f502,f140,f972,f968,f572,f964])).
% 1.56/0.57  fof(f572,plain,(
% 1.56/0.57    spl8_6 <=> v1_xboole_0(k1_xboole_0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.56/0.57  fof(f502,plain,(
% 1.56/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0) | ~spl8_1),
% 1.56/0.57    inference(forward_demodulation,[],[f460,f421])).
% 1.56/0.57  fof(f460,plain,(
% 1.56/0.57    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0) | ~spl8_1),
% 1.56/0.57    inference(backward_demodulation,[],[f417,f421])).
% 1.56/0.57  fof(f417,plain,(
% 1.56/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(sK2) | v1_xboole_0(sK0)),
% 1.56/0.57    inference(forward_demodulation,[],[f416,f90])).
% 1.56/0.57  fof(f416,plain,(
% 1.56/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(sK2) | v1_xboole_0(sK0)),
% 1.56/0.57    inference(forward_demodulation,[],[f347,f313])).
% 1.56/0.57  fof(f347,plain,(
% 1.56/0.57    ~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0)),
% 1.56/0.57    inference(backward_demodulation,[],[f246,f313])).
% 1.56/0.57  fof(f246,plain,(
% 1.56/0.57    ~v1_xboole_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0)),
% 1.56/0.57    inference(resolution,[],[f234,f63])).
% 1.56/0.57  fof(f63,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~v1_xboole_0(X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.56/0.57    inference(flattening,[],[f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.56/0.57    inference(ennf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).
% 1.56/0.57  fof(f234,plain,(
% 1.56/0.57    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f122,f75])).
% 1.56/0.57  fof(f75,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.57  fof(f583,plain,(
% 1.56/0.57    spl8_6),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f576])).
% 1.56/0.57  fof(f576,plain,(
% 1.56/0.57    $false | spl8_6),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f77,f574])).
% 1.56/0.57  fof(f574,plain,(
% 1.56/0.57    ~v1_xboole_0(k1_xboole_0) | spl8_6),
% 1.56/0.57    inference(avatar_component_clause,[],[f572])).
% 1.56/0.57  fof(f77,plain,(
% 1.56/0.57    v1_xboole_0(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    v1_xboole_0(k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.57  fof(f414,plain,(
% 1.56/0.57    spl8_2),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f407])).
% 1.56/0.57  fof(f407,plain,(
% 1.56/0.57    $false | spl8_2),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f77,f377])).
% 1.56/0.57  fof(f377,plain,(
% 1.56/0.57    ~v1_xboole_0(k1_xboole_0) | spl8_2),
% 1.56/0.57    inference(forward_demodulation,[],[f328,f90])).
% 1.56/0.57  fof(f328,plain,(
% 1.56/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | spl8_2),
% 1.56/0.57    inference(backward_demodulation,[],[f183,f313])).
% 1.56/0.57  fof(f183,plain,(
% 1.56/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl8_2),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f166,f75])).
% 1.56/0.57  fof(f166,plain,(
% 1.56/0.57    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1)) | spl8_2),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f146,f52])).
% 1.56/0.57  fof(f146,plain,(
% 1.56/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl8_2),
% 1.56/0.57    inference(avatar_component_clause,[],[f144])).
% 1.56/0.57  fof(f144,plain,(
% 1.56/0.57    spl8_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.56/0.57  fof(f147,plain,(
% 1.56/0.57    spl8_1 | ~spl8_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f99,f144,f140])).
% 1.56/0.57  fof(f99,plain,(
% 1.56/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.56/0.57    inference(resolution,[],[f94,f56])).
% 1.56/0.57  fof(f94,plain,(
% 1.56/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f35,f50])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (16165)------------------------------
% 1.56/0.57  % (16165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (16165)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (16165)Memory used [KB]: 6524
% 1.56/0.57  % (16165)Time elapsed: 0.164 s
% 1.56/0.57  % (16165)------------------------------
% 1.56/0.57  % (16165)------------------------------
% 1.56/0.57  % (16192)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.60  % (16157)Success in time 0.23 s
%------------------------------------------------------------------------------
