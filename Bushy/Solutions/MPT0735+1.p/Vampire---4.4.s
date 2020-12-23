%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t23_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 8.01s
% Output     : Refutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 296 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  222 ( 789 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9839,f16420])).

fof(f16420,plain,(
    spl9_11 ),
    inference(avatar_contradiction_clause,[],[f16402])).

fof(f16402,plain,
    ( $false
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f10532,f15897,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d5_xboole_0)).

fof(f15897,plain,
    ( r2_hidden(sK0,sK6(sK0))
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f15881,f10377])).

fof(f10377,plain,
    ( r2_hidden(sK8(sK6(sK0),sK0),sK6(sK0))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f9975,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d3_tarski)).

fof(f9975,plain,
    ( ~ r1_tarski(sK6(sK0),sK0)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f4775,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d2_ordinal1)).

fof(f4775,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f4774])).

fof(f4774,plain,
    ( spl9_11
  <=> ~ v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f15881,plain,
    ( sK0 = sK8(sK6(sK0),sK0)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f51,f10378,f14928,f14944,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X1,X2)
      | X1 = X2
      | r2_hidden(X2,X1)
      | ~ v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d3_ordinal1)).

fof(f14944,plain,
    ( r2_hidden(sK8(sK6(sK0),sK0),sK1)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f10576,f10377,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t4_subset)).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t2_subset)).

fof(f104,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t7_boole)).

fof(f10576,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(sK1))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f10557,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t3_subset)).

fof(f10557,plain,
    ( r1_tarski(sK6(sK0),sK1)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f92,f10362,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10362,plain,
    ( r2_hidden(sK6(sK0),sK1)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f9974,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9974,plain,
    ( r2_hidden(sK6(sK0),sK0)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f4775,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f92,f51,f71])).

fof(f92,plain,(
    v1_ordinal1(sK1) ),
    inference(unit_resulting_resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',cc1_ordinal1)).

fof(f50,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r2_hidden(X0,X1)
         => v3_ordinal1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t23_ordinal1)).

fof(f14928,plain,
    ( ~ r2_hidden(sK0,sK8(sK6(sK0),sK0))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f9974,f10377,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t3_ordinal1)).

fof(f10378,plain,
    ( ~ r2_hidden(sK8(sK6(sK0),sK0),sK0)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f9975,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f51,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    v2_ordinal1(sK1) ),
    inference(unit_resulting_resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10532,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK6(sK0)))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f51,f10358,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f10358,plain,
    ( ~ r2_hidden(sK0,sK6(sK0))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f9974,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',antisymmetry_r2_hidden)).

fof(f9839,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f9836])).

fof(f9836,plain,
    ( $false
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f8437,f8374,f8147,f8148,f8149,f65])).

fof(f8149,plain,
    ( ~ r2_hidden(sK5(sK0),sK4(sK0))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f8093,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0),sK4(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8093,plain,
    ( ~ v2_ordinal1(sK0)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f52,f4772,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',cc2_ordinal1)).

fof(f4772,plain,
    ( v1_ordinal1(sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f4771])).

fof(f4771,plain,
    ( spl9_10
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f52,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f8148,plain,
    ( sK4(sK0) != sK5(sK0)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f8093,f69])).

fof(f69,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8147,plain,
    ( ~ r2_hidden(sK4(sK0),sK5(sK0))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f8093,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),sK5(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8374,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f103,f8145,f86])).

fof(f8145,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f8093,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8437,plain,
    ( r2_hidden(sK5(sK0),sK1)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f103,f8146,f86])).

fof(f8146,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f8093,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
