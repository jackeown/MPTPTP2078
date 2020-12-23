%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:28 EST 2020

% Result     : Theorem 3.58s
% Output     : Refutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 869 expanded)
%              Number of leaves         :   24 ( 224 expanded)
%              Depth                    :   17
%              Number of atoms          :  374 (1901 expanded)
%              Number of equality atoms :   97 ( 696 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f659,f4939,f5421,f5552,f5576])).

fof(f5576,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f5571])).

fof(f5571,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f99,f264,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f264,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_2
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f94,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f5552,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f5540])).

fof(f5540,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f99,f5431,f93])).

fof(f5431,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f2616,f4082])).

fof(f4082,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f4081,f100])).

fof(f100,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f95,f96])).

fof(f96,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f85,f75])).

fof(f85,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f95,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f4081,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f3767,f3768])).

fof(f3768,plain,
    ( k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f1853,f3717,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f3717,plain,
    ( ! [X0] : m1_subset_1(k7_setfam_1(k1_xboole_0,k1_xboole_0),X0)
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f99,f3588,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3588,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f1849,f3566])).

fof(f3566,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f3564])).

fof(f3564,plain,
    ( spl6_17
  <=> k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1849,plain,(
    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f1841,f110])).

fof(f110,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1841,plain,(
    r1_tarski(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f1833,f93])).

fof(f1833,plain,(
    m1_subset_1(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f99,f729])).

fof(f729,plain,(
    ! [X2] :
      ( m1_subset_1(k7_setfam_1(k1_xboole_0,X2),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_tarski(k1_xboole_0))) ) ),
    inference(superposition,[],[f68,f76])).

fof(f76,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f1853,plain,(
    k1_xboole_0 = k7_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f99,f730])).

fof(f730,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_tarski(k1_xboole_0)))
      | k7_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,X3)) = X3 ) ),
    inference(superposition,[],[f69,f76])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f3767,plain,
    ( ! [X0] : k7_setfam_1(k1_xboole_0,k1_xboole_0) = k3_subset_1(X0,k3_subset_1(X0,k7_setfam_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f3717,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2616,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),k1_xboole_0)
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f2595,f738])).

fof(f738,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | r2_hidden(X12,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[],[f110,f76])).

fof(f2595,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK0),k1_tarski(k1_xboole_0))
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f127,f1974,f752,f1683,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f1683,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_tarski(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f752,f68])).

fof(f752,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f683,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f683,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f265,f110])).

fof(f265,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f263])).

fof(f1974,plain,
    ( ~ r2_hidden(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f1735,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f81,f58])).

fof(f58,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f1735,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k7_setfam_1(sK0,k1_tarski(k1_xboole_0))))
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f1718,f93])).

fof(f1718,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f1716,f118])).

fof(f118,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f69])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1716,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f752,f117,f1600,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f1600,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f59,f693,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f693,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f269,f57,f67])).

fof(f269,plain,
    ( k1_xboole_0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f59,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f57,f68])).

fof(f127,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f112,f86])).

fof(f112,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f107,f58])).

fof(f107,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f5421,plain,
    ( ~ spl6_10
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f5411])).

fof(f5411,plain,
    ( $false
    | ~ spl6_10
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f5312,f2835])).

fof(f2835,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f2825,f2784])).

fof(f2784,plain,
    ( k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f2708])).

fof(f2708,plain,
    ( k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f1850,f2075])).

fof(f2075,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f2073])).

fof(f2073,plain,
    ( spl6_10
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1850,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f1841,f70])).

fof(f2825,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f2707,f2642])).

fof(f2642,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f76,f2075])).

fof(f2707,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f1849,f2075])).

fof(f5312,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | spl6_17 ),
    inference(forward_demodulation,[],[f5095,f2642])).

fof(f5095,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_10
    | spl6_17 ),
    inference(backward_demodulation,[],[f4223,f4940])).

fof(f4940,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f76,f2642])).

fof(f4223,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f3565,f105])).

fof(f105,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3565,plain,
    ( k1_xboole_0 != k1_zfmisc_1(k1_tarski(k1_xboole_0))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f3564])).

fof(f4939,plain,
    ( ~ spl6_2
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f4936])).

fof(f4936,plain,
    ( $false
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f112,f4934])).

fof(f4934,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_2
    | spl6_10 ),
    inference(forward_demodulation,[],[f4933,f100])).

fof(f4933,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f99,f57,f117,f4922,f102])).

fof(f4922,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f4469,f81])).

fof(f4469,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(sK0,sK1)))
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f3560,f93])).

fof(f3560,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k7_setfam_1(sK0,sK1))
    | ~ spl6_2
    | spl6_10 ),
    inference(forward_demodulation,[],[f3535,f1684])).

fof(f1684,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f752,f69])).

fof(f3535,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))),k7_setfam_1(sK0,sK1))
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f57,f3077,f1683,f65])).

fof(f3077,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,k1_tarski(k1_xboole_0)),sK1)
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f1693,f3037,f114])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | sK1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f70,f58])).

fof(f3037,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | ~ spl6_2
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f2074,f752,f67])).

fof(f2074,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f2073])).

fof(f1693,plain,
    ( sK1 != k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f1682,f118])).

fof(f1682,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_setfam_1(sK0,k1_tarski(k1_xboole_0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f59,f117,f752,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_setfam_1)).

fof(f659,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f501,f513])).

fof(f513,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f512,f477])).

fof(f477,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f76,f433])).

fof(f433,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f277,f423])).

fof(f423,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f127,f415,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f75])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f415,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f396,f93])).

fof(f396,plain,
    ( ! [X0] : m1_subset_1(sK0,X0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f99,f280,f86])).

fof(f280,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f112,f270])).

fof(f270,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f268])).

fof(f277,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f58,f270])).

fof(f512,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f451,f477])).

fof(f451,plain,
    ( r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f329,f423])).

fof(f329,plain,
    ( r2_hidden(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f239,f270])).

fof(f239,plain,(
    r2_hidden(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f227,f110])).

fof(f227,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f117,f93])).

fof(f501,plain,
    ( ~ r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f500,f433])).

fof(f500,plain,
    ( ~ r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f444,f433])).

fof(f444,plain,
    ( ~ r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f296,f423])).

fof(f296,plain,
    ( ~ r2_hidden(k7_setfam_1(sK0,k1_xboole_0),k1_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f142,f270])).

fof(f142,plain,(
    ~ r2_hidden(k7_setfam_1(sK0,sK1),k1_tarski(k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f59,f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (22098)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (22089)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (22096)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (22081)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22085)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (22079)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (22088)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (22086)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (22104)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (22087)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (22102)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (22090)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (22077)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22076)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (22100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (22094)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (22082)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (22080)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (22078)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (22083)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (22092)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (22075)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (22099)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (22084)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (22103)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (22101)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (22091)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.56  % (22097)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.45/0.56  % (22091)Refutation not found, incomplete strategy% (22091)------------------------------
% 1.45/0.56  % (22091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (22091)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (22091)Memory used [KB]: 10746
% 1.45/0.56  % (22091)Time elapsed: 0.140 s
% 1.45/0.56  % (22091)------------------------------
% 1.45/0.56  % (22091)------------------------------
% 1.45/0.56  % (22095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (22093)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.18/0.69  % (22105)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.95/0.82  % (22099)Time limit reached!
% 2.95/0.82  % (22099)------------------------------
% 2.95/0.82  % (22099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.82  % (22099)Termination reason: Time limit
% 2.95/0.82  % (22099)Termination phase: Saturation
% 2.95/0.82  
% 2.95/0.82  % (22099)Memory used [KB]: 12281
% 2.95/0.82  % (22099)Time elapsed: 0.400 s
% 2.95/0.82  % (22099)------------------------------
% 2.95/0.82  % (22099)------------------------------
% 2.95/0.84  % (22077)Time limit reached!
% 2.95/0.84  % (22077)------------------------------
% 2.95/0.84  % (22077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.84  % (22077)Termination reason: Time limit
% 2.95/0.84  
% 2.95/0.84  % (22077)Memory used [KB]: 6652
% 2.95/0.84  % (22077)Time elapsed: 0.417 s
% 2.95/0.84  % (22077)------------------------------
% 2.95/0.84  % (22077)------------------------------
% 3.58/0.86  % (22100)Refutation found. Thanks to Tanya!
% 3.58/0.86  % SZS status Theorem for theBenchmark
% 3.58/0.86  % SZS output start Proof for theBenchmark
% 3.58/0.86  fof(f5577,plain,(
% 3.58/0.86    $false),
% 3.58/0.86    inference(avatar_sat_refutation,[],[f659,f4939,f5421,f5552,f5576])).
% 3.58/0.86  fof(f5576,plain,(
% 3.58/0.86    spl6_2),
% 3.58/0.86    inference(avatar_contradiction_clause,[],[f5571])).
% 3.58/0.86  fof(f5571,plain,(
% 3.58/0.86    $false | spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f264,f93])).
% 3.58/0.86  fof(f93,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.58/0.86    inference(cnf_transformation,[],[f30])).
% 3.58/0.86  fof(f30,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.58/0.86  fof(f264,plain,(
% 3.58/0.86    ~r1_tarski(k1_xboole_0,sK0) | spl6_2),
% 3.58/0.86    inference(avatar_component_clause,[],[f263])).
% 3.58/0.86  fof(f263,plain,(
% 3.58/0.86    spl6_2 <=> r1_tarski(k1_xboole_0,sK0)),
% 3.58/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.58/0.86  fof(f99,plain,(
% 3.58/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.58/0.86    inference(definition_unfolding,[],[f94,f75])).
% 3.58/0.86  fof(f75,plain,(
% 3.58/0.86    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.58/0.86    inference(cnf_transformation,[],[f17])).
% 3.58/0.86  fof(f17,axiom,(
% 3.58/0.86    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 3.58/0.86  fof(f94,plain,(
% 3.58/0.86    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f19])).
% 3.58/0.86  fof(f19,axiom,(
% 3.58/0.86    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 3.58/0.86  fof(f5552,plain,(
% 3.58/0.86    ~spl6_2 | spl6_3 | ~spl6_17),
% 3.58/0.86    inference(avatar_contradiction_clause,[],[f5540])).
% 3.58/0.86  fof(f5540,plain,(
% 3.58/0.86    $false | (~spl6_2 | spl6_3 | ~spl6_17)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f5431,f93])).
% 3.58/0.86  fof(f5431,plain,(
% 3.58/0.86    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_2 | spl6_3 | ~spl6_17)),
% 3.58/0.86    inference(backward_demodulation,[],[f2616,f4082])).
% 3.58/0.86  fof(f4082,plain,(
% 3.58/0.86    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | ~spl6_17),
% 3.58/0.86    inference(forward_demodulation,[],[f4081,f100])).
% 3.58/0.86  fof(f100,plain,(
% 3.58/0.86    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.58/0.86    inference(definition_unfolding,[],[f95,f96])).
% 3.58/0.86  fof(f96,plain,(
% 3.58/0.86    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.58/0.86    inference(definition_unfolding,[],[f85,f75])).
% 3.58/0.86  fof(f85,plain,(
% 3.58/0.86    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f21])).
% 3.58/0.86  fof(f21,axiom,(
% 3.58/0.86    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 3.58/0.86  fof(f95,plain,(
% 3.58/0.86    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.58/0.86    inference(cnf_transformation,[],[f18])).
% 3.58/0.86  fof(f18,axiom,(
% 3.58/0.86    ! [X0] : k2_subset_1(X0) = X0),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 3.58/0.86  fof(f4081,plain,(
% 3.58/0.86    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) ) | ~spl6_17),
% 3.58/0.86    inference(forward_demodulation,[],[f3767,f3768])).
% 3.58/0.86  fof(f3768,plain,(
% 3.58/0.86    k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0) | ~spl6_17),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1853,f3717,f67])).
% 3.58/0.86  fof(f67,plain,(
% 3.58/0.86    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f45])).
% 3.58/0.86  fof(f45,plain,(
% 3.58/0.86    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(flattening,[],[f44])).
% 3.58/0.86  fof(f44,plain,(
% 3.58/0.86    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f31])).
% 3.58/0.86  fof(f31,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 3.58/0.86  fof(f3717,plain,(
% 3.58/0.86    ( ! [X0] : (m1_subset_1(k7_setfam_1(k1_xboole_0,k1_xboole_0),X0)) ) | ~spl6_17),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f3588,f86])).
% 3.58/0.86  fof(f86,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 3.58/0.86    inference(cnf_transformation,[],[f55])).
% 3.58/0.86  fof(f55,plain,(
% 3.58/0.86    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.58/0.86    inference(flattening,[],[f54])).
% 3.58/0.86  fof(f54,plain,(
% 3.58/0.86    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.58/0.86    inference(ennf_transformation,[],[f32])).
% 3.58/0.86  fof(f32,axiom,(
% 3.58/0.86    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 3.58/0.86  fof(f3588,plain,(
% 3.58/0.86    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_17),
% 3.58/0.86    inference(backward_demodulation,[],[f1849,f3566])).
% 3.58/0.86  fof(f3566,plain,(
% 3.58/0.86    k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) | ~spl6_17),
% 3.58/0.86    inference(avatar_component_clause,[],[f3564])).
% 3.58/0.86  fof(f3564,plain,(
% 3.58/0.86    spl6_17 <=> k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0))),
% 3.58/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.58/0.86  fof(f1849,plain,(
% 3.58/0.86    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1841,f110])).
% 3.58/0.86  fof(f110,plain,(
% 3.58/0.86    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 3.58/0.86    inference(equality_resolution,[],[f87])).
% 3.58/0.86  fof(f87,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.58/0.86    inference(cnf_transformation,[],[f13])).
% 3.58/0.86  fof(f13,axiom,(
% 3.58/0.86    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.58/0.86  fof(f1841,plain,(
% 3.58/0.86    r1_tarski(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_xboole_0))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1833,f93])).
% 3.58/0.86  fof(f1833,plain,(
% 3.58/0.86    m1_subset_1(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f729])).
% 3.58/0.86  fof(f729,plain,(
% 3.58/0.86    ( ! [X2] : (m1_subset_1(k7_setfam_1(k1_xboole_0,X2),k1_zfmisc_1(k1_tarski(k1_xboole_0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_tarski(k1_xboole_0)))) )),
% 3.58/0.86    inference(superposition,[],[f68,f76])).
% 3.58/0.86  fof(f76,plain,(
% 3.58/0.86    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 3.58/0.86    inference(cnf_transformation,[],[f15])).
% 3.58/0.86  fof(f15,axiom,(
% 3.58/0.86    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 3.58/0.86  fof(f68,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f46])).
% 3.58/0.86  fof(f46,plain,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f26])).
% 3.58/0.86  fof(f26,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 3.58/0.86  fof(f1853,plain,(
% 3.58/0.86    k1_xboole_0 = k7_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,k1_xboole_0))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f730])).
% 3.58/0.86  fof(f730,plain,(
% 3.58/0.86    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_tarski(k1_xboole_0))) | k7_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,X3)) = X3) )),
% 3.58/0.86    inference(superposition,[],[f69,f76])).
% 3.58/0.86  fof(f69,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 3.58/0.86    inference(cnf_transformation,[],[f47])).
% 3.58/0.86  fof(f47,plain,(
% 3.58/0.86    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f27])).
% 3.58/0.86  fof(f27,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 3.58/0.86  fof(f3767,plain,(
% 3.58/0.86    ( ! [X0] : (k7_setfam_1(k1_xboole_0,k1_xboole_0) = k3_subset_1(X0,k3_subset_1(X0,k7_setfam_1(k1_xboole_0,k1_xboole_0)))) ) | ~spl6_17),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f3717,f84])).
% 3.58/0.86  fof(f84,plain,(
% 3.58/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f53])).
% 3.58/0.86  fof(f53,plain,(
% 3.58/0.86    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.86    inference(ennf_transformation,[],[f20])).
% 3.58/0.86  fof(f20,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.58/0.86  fof(f2616,plain,(
% 3.58/0.86    ~r1_tarski(k3_subset_1(sK0,sK0),k1_xboole_0) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f2595,f738])).
% 3.58/0.86  fof(f738,plain,(
% 3.58/0.86    ( ! [X12] : (~r1_tarski(X12,k1_xboole_0) | r2_hidden(X12,k1_tarski(k1_xboole_0))) )),
% 3.58/0.86    inference(superposition,[],[f110,f76])).
% 3.58/0.86  fof(f2595,plain,(
% 3.58/0.86    ~r2_hidden(k3_subset_1(sK0,sK0),k1_tarski(k1_xboole_0)) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f127,f1974,f752,f1683,f102])).
% 3.58/0.86  fof(f102,plain,(
% 3.58/0.86    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 3.58/0.86    inference(equality_resolution,[],[f62])).
% 3.58/0.86  fof(f62,plain,(
% 3.58/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 3.58/0.86    inference(cnf_transformation,[],[f39])).
% 3.58/0.86  fof(f39,plain,(
% 3.58/0.86    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f25])).
% 3.58/0.86  fof(f25,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 3.58/0.86  fof(f1683,plain,(
% 3.58/0.86    m1_subset_1(k7_setfam_1(sK0,k1_tarski(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f752,f68])).
% 3.58/0.86  fof(f752,plain,(
% 3.58/0.86    m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f683,f81])).
% 3.58/0.86  fof(f81,plain,(
% 3.58/0.86    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.58/0.86    inference(cnf_transformation,[],[f51])).
% 3.58/0.86  fof(f51,plain,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.58/0.86    inference(ennf_transformation,[],[f24])).
% 3.58/0.86  fof(f24,axiom,(
% 3.58/0.86    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 3.58/0.86  fof(f683,plain,(
% 3.58/0.86    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f265,f110])).
% 3.58/0.86  fof(f265,plain,(
% 3.58/0.86    r1_tarski(k1_xboole_0,sK0) | ~spl6_2),
% 3.58/0.86    inference(avatar_component_clause,[],[f263])).
% 3.58/0.86  fof(f1974,plain,(
% 3.58/0.86    ~r2_hidden(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1735,f111])).
% 3.58/0.86  fof(f111,plain,(
% 3.58/0.86    ( ! [X0] : (~r2_hidden(sK0,X0) | m1_subset_1(sK1,k1_zfmisc_1(X0))) )),
% 3.58/0.86    inference(superposition,[],[f81,f58])).
% 3.58/0.86  fof(f58,plain,(
% 3.58/0.86    sK1 = k1_tarski(sK0)),
% 3.58/0.86    inference(cnf_transformation,[],[f38])).
% 3.58/0.86  fof(f38,plain,(
% 3.58/0.86    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(flattening,[],[f37])).
% 3.58/0.86  fof(f37,plain,(
% 3.58/0.86    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f36])).
% 3.58/0.86  fof(f36,negated_conjecture,(
% 3.58/0.86    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 3.58/0.86    inference(negated_conjecture,[],[f35])).
% 3.58/0.86  fof(f35,conjecture,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).
% 3.58/0.86  fof(f1735,plain,(
% 3.58/0.86    ~m1_subset_1(sK1,k1_zfmisc_1(k7_setfam_1(sK0,k1_tarski(k1_xboole_0)))) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1718,f93])).
% 3.58/0.86  fof(f1718,plain,(
% 3.58/0.86    ~r1_tarski(sK1,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(forward_demodulation,[],[f1716,f118])).
% 3.58/0.86  fof(f118,plain,(
% 3.58/0.86    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f57,f69])).
% 3.58/0.86  fof(f57,plain,(
% 3.58/0.86    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 3.58/0.86    inference(cnf_transformation,[],[f38])).
% 3.58/0.86  fof(f1716,plain,(
% 3.58/0.86    ~r1_tarski(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | (~spl6_2 | spl6_3)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f752,f117,f1600,f65])).
% 3.58/0.86  fof(f65,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r1_tarski(X1,X2)) )),
% 3.58/0.86    inference(cnf_transformation,[],[f41])).
% 3.58/0.86  fof(f41,plain,(
% 3.58/0.86    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(flattening,[],[f40])).
% 3.58/0.86  fof(f40,plain,(
% 3.58/0.86    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f33])).
% 3.58/0.86  fof(f33,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).
% 3.58/0.86  fof(f1600,plain,(
% 3.58/0.86    ~r1_tarski(k7_setfam_1(sK0,sK1),k1_tarski(k1_xboole_0)) | spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f59,f693,f70])).
% 3.58/0.86  fof(f70,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 3.58/0.86    inference(cnf_transformation,[],[f14])).
% 3.58/0.86  fof(f14,axiom,(
% 3.58/0.86    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 3.58/0.86  fof(f693,plain,(
% 3.58/0.86    k1_xboole_0 != k7_setfam_1(sK0,sK1) | spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f269,f57,f67])).
% 3.58/0.86  fof(f269,plain,(
% 3.58/0.86    k1_xboole_0 != sK1 | spl6_3),
% 3.58/0.86    inference(avatar_component_clause,[],[f268])).
% 3.58/0.86  fof(f268,plain,(
% 3.58/0.86    spl6_3 <=> k1_xboole_0 = sK1),
% 3.58/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.58/0.86  fof(f59,plain,(
% 3.58/0.86    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 3.58/0.86    inference(cnf_transformation,[],[f38])).
% 3.58/0.86  fof(f117,plain,(
% 3.58/0.86    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f57,f68])).
% 3.58/0.86  fof(f127,plain,(
% 3.58/0.86    m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f57,f112,f86])).
% 3.58/0.86  fof(f112,plain,(
% 3.58/0.86    r2_hidden(sK0,sK1)),
% 3.58/0.86    inference(superposition,[],[f107,f58])).
% 3.58/0.86  fof(f107,plain,(
% 3.58/0.86    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 3.58/0.86    inference(equality_resolution,[],[f106])).
% 3.58/0.86  fof(f106,plain,(
% 3.58/0.86    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 3.58/0.86    inference(equality_resolution,[],[f77])).
% 3.58/0.86  fof(f77,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 3.58/0.86    inference(cnf_transformation,[],[f5])).
% 3.58/0.86  fof(f5,axiom,(
% 3.58/0.86    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 3.58/0.86  fof(f5421,plain,(
% 3.58/0.86    ~spl6_10 | spl6_17),
% 3.58/0.86    inference(avatar_contradiction_clause,[],[f5411])).
% 3.58/0.86  fof(f5411,plain,(
% 3.58/0.86    $false | (~spl6_10 | spl6_17)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f5312,f2835])).
% 3.58/0.86  fof(f2835,plain,(
% 3.58/0.86    r2_hidden(k1_xboole_0,k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(backward_demodulation,[],[f2825,f2784])).
% 3.58/0.86  fof(f2784,plain,(
% 3.58/0.86    k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(duplicate_literal_removal,[],[f2708])).
% 3.58/0.86  fof(f2708,plain,(
% 3.58/0.86    k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(backward_demodulation,[],[f1850,f2075])).
% 3.58/0.86  fof(f2075,plain,(
% 3.58/0.86    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(avatar_component_clause,[],[f2073])).
% 3.58/0.86  fof(f2073,plain,(
% 3.58/0.86    spl6_10 <=> k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 3.58/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 3.58/0.86  fof(f1850,plain,(
% 3.58/0.86    k1_tarski(k1_xboole_0) = k7_setfam_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k7_setfam_1(k1_xboole_0,k1_xboole_0)),
% 3.58/0.86    inference(resolution,[],[f1841,f70])).
% 3.58/0.86  fof(f2825,plain,(
% 3.58/0.86    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(forward_demodulation,[],[f2707,f2642])).
% 3.58/0.86  fof(f2642,plain,(
% 3.58/0.86    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(backward_demodulation,[],[f76,f2075])).
% 3.58/0.86  fof(f2707,plain,(
% 3.58/0.86    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_10),
% 3.58/0.86    inference(backward_demodulation,[],[f1849,f2075])).
% 3.58/0.86  fof(f5312,plain,(
% 3.58/0.86    ~r2_hidden(k1_xboole_0,k1_xboole_0) | (~spl6_10 | spl6_17)),
% 3.58/0.86    inference(forward_demodulation,[],[f5095,f2642])).
% 3.58/0.86  fof(f5095,plain,(
% 3.58/0.86    ~r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (~spl6_10 | spl6_17)),
% 3.58/0.86    inference(backward_demodulation,[],[f4223,f4940])).
% 3.58/0.86  fof(f4940,plain,(
% 3.58/0.86    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl6_10),
% 3.58/0.86    inference(backward_demodulation,[],[f76,f2642])).
% 3.58/0.86  fof(f4223,plain,(
% 3.58/0.86    ~r2_hidden(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) | spl6_17),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f3565,f105])).
% 3.58/0.86  fof(f105,plain,(
% 3.58/0.86    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 3.58/0.86    inference(equality_resolution,[],[f78])).
% 3.58/0.86  fof(f78,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 3.58/0.86    inference(cnf_transformation,[],[f5])).
% 3.58/0.86  fof(f3565,plain,(
% 3.58/0.86    k1_xboole_0 != k1_zfmisc_1(k1_tarski(k1_xboole_0)) | spl6_17),
% 3.58/0.86    inference(avatar_component_clause,[],[f3564])).
% 3.58/0.86  fof(f4939,plain,(
% 3.58/0.86    ~spl6_2 | spl6_10),
% 3.58/0.86    inference(avatar_contradiction_clause,[],[f4936])).
% 3.58/0.86  fof(f4936,plain,(
% 3.58/0.86    $false | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f112,f4934])).
% 3.58/0.86  fof(f4934,plain,(
% 3.58/0.86    ~r2_hidden(sK0,sK1) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(forward_demodulation,[],[f4933,f100])).
% 3.58/0.86  fof(f4933,plain,(
% 3.58/0.86    ~r2_hidden(k3_subset_1(sK0,k1_xboole_0),sK1) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f57,f117,f4922,f102])).
% 3.58/0.86  fof(f4922,plain,(
% 3.58/0.86    ~r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f4469,f81])).
% 3.58/0.86  fof(f4469,plain,(
% 3.58/0.86    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(sK0,sK1))) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f3560,f93])).
% 3.58/0.86  fof(f3560,plain,(
% 3.58/0.86    ~r1_tarski(k1_tarski(k1_xboole_0),k7_setfam_1(sK0,sK1)) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(forward_demodulation,[],[f3535,f1684])).
% 3.58/0.86  fof(f1684,plain,(
% 3.58/0.86    k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))) | ~spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f752,f69])).
% 3.58/0.86  fof(f3535,plain,(
% 3.58/0.86    ~r1_tarski(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_tarski(k1_xboole_0))),k7_setfam_1(sK0,sK1)) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f57,f3077,f1683,f65])).
% 3.58/0.86  fof(f3077,plain,(
% 3.58/0.86    ~r1_tarski(k7_setfam_1(sK0,k1_tarski(k1_xboole_0)),sK1) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f1693,f3037,f114])).
% 3.58/0.86  fof(f114,plain,(
% 3.58/0.86    ( ! [X2] : (~r1_tarski(X2,sK1) | sK1 = X2 | k1_xboole_0 = X2) )),
% 3.58/0.86    inference(superposition,[],[f70,f58])).
% 3.58/0.86  fof(f3037,plain,(
% 3.58/0.86    k1_xboole_0 != k7_setfam_1(sK0,k1_tarski(k1_xboole_0)) | (~spl6_2 | spl6_10)),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f2074,f752,f67])).
% 3.58/0.86  fof(f2074,plain,(
% 3.58/0.86    k1_xboole_0 != k1_tarski(k1_xboole_0) | spl6_10),
% 3.58/0.86    inference(avatar_component_clause,[],[f2073])).
% 3.58/0.86  fof(f1693,plain,(
% 3.58/0.86    sK1 != k7_setfam_1(sK0,k1_tarski(k1_xboole_0)) | ~spl6_2),
% 3.58/0.86    inference(forward_demodulation,[],[f1682,f118])).
% 3.58/0.86  fof(f1682,plain,(
% 3.58/0.86    k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_setfam_1(sK0,k1_tarski(k1_xboole_0)) | ~spl6_2),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f59,f117,f752,f66])).
% 3.58/0.86  fof(f66,plain,(
% 3.58/0.86    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X1 = X2) )),
% 3.58/0.86    inference(cnf_transformation,[],[f43])).
% 3.58/0.86  fof(f43,plain,(
% 3.58/0.86    ! [X0,X1] : (! [X2] : (X1 = X2 | k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(flattening,[],[f42])).
% 3.58/0.86  fof(f42,plain,(
% 3.58/0.86    ! [X0,X1] : (! [X2] : ((X1 = X2 | k7_setfam_1(X0,X1) != k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.58/0.86    inference(ennf_transformation,[],[f34])).
% 3.58/0.86  fof(f34,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2) => X1 = X2)))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_setfam_1)).
% 3.58/0.86  fof(f659,plain,(
% 3.58/0.86    ~spl6_3),
% 3.58/0.86    inference(avatar_contradiction_clause,[],[f651])).
% 3.58/0.86  fof(f651,plain,(
% 3.58/0.86    $false | ~spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f501,f513])).
% 3.58/0.86  fof(f513,plain,(
% 3.58/0.86    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_3),
% 3.58/0.86    inference(forward_demodulation,[],[f512,f477])).
% 3.58/0.86  fof(f477,plain,(
% 3.58/0.86    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | ~spl6_3),
% 3.58/0.86    inference(backward_demodulation,[],[f76,f433])).
% 3.58/0.86  fof(f433,plain,(
% 3.58/0.86    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl6_3),
% 3.58/0.86    inference(backward_demodulation,[],[f277,f423])).
% 3.58/0.86  fof(f423,plain,(
% 3.58/0.86    k1_xboole_0 = sK0 | ~spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f127,f415,f97])).
% 3.58/0.86  fof(f97,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.86    inference(definition_unfolding,[],[f83,f75])).
% 3.58/0.86  fof(f83,plain,(
% 3.58/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 3.58/0.86    inference(cnf_transformation,[],[f52])).
% 3.58/0.86  fof(f52,plain,(
% 3.58/0.86    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.86    inference(ennf_transformation,[],[f22])).
% 3.58/0.86  fof(f22,axiom,(
% 3.58/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.58/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 3.58/0.86  fof(f415,plain,(
% 3.58/0.86    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f396,f93])).
% 3.58/0.86  fof(f396,plain,(
% 3.58/0.86    ( ! [X0] : (m1_subset_1(sK0,X0)) ) | ~spl6_3),
% 3.58/0.86    inference(unit_resulting_resolution,[],[f99,f280,f86])).
% 3.58/0.86  fof(f280,plain,(
% 3.58/0.86    r2_hidden(sK0,k1_xboole_0) | ~spl6_3),
% 3.58/0.86    inference(backward_demodulation,[],[f112,f270])).
% 3.87/0.88  fof(f270,plain,(
% 3.87/0.88    k1_xboole_0 = sK1 | ~spl6_3),
% 3.87/0.88    inference(avatar_component_clause,[],[f268])).
% 3.87/0.88  fof(f277,plain,(
% 3.87/0.88    k1_xboole_0 = k1_tarski(sK0) | ~spl6_3),
% 3.87/0.88    inference(backward_demodulation,[],[f58,f270])).
% 3.87/0.88  fof(f512,plain,(
% 3.87/0.88    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_3),
% 3.87/0.88    inference(forward_demodulation,[],[f451,f477])).
% 3.87/0.88  fof(f451,plain,(
% 3.87/0.88    r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~spl6_3),
% 3.87/0.88    inference(backward_demodulation,[],[f329,f423])).
% 3.87/0.88  fof(f329,plain,(
% 3.87/0.88    r2_hidden(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_3),
% 3.87/0.88    inference(backward_demodulation,[],[f239,f270])).
% 3.87/0.88  fof(f239,plain,(
% 3.87/0.88    r2_hidden(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 3.87/0.88    inference(unit_resulting_resolution,[],[f227,f110])).
% 3.87/0.88  fof(f227,plain,(
% 3.87/0.88    r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 3.87/0.88    inference(unit_resulting_resolution,[],[f117,f93])).
% 3.87/0.88  fof(f501,plain,(
% 3.87/0.88    ~r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_3),
% 3.87/0.88    inference(forward_demodulation,[],[f500,f433])).
% 3.87/0.88  fof(f500,plain,(
% 3.87/0.88    ~r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_xboole_0)) | ~spl6_3),
% 3.87/0.88    inference(forward_demodulation,[],[f444,f433])).
% 3.87/0.88  fof(f444,plain,(
% 3.87/0.88    ~r2_hidden(k7_setfam_1(k1_xboole_0,k1_xboole_0),k1_tarski(k1_tarski(k1_xboole_0))) | ~spl6_3),
% 3.87/0.88    inference(backward_demodulation,[],[f296,f423])).
% 3.87/0.88  fof(f296,plain,(
% 3.87/0.88    ~r2_hidden(k7_setfam_1(sK0,k1_xboole_0),k1_tarski(k1_tarski(k1_xboole_0))) | ~spl6_3),
% 3.87/0.88    inference(backward_demodulation,[],[f142,f270])).
% 3.87/0.88  fof(f142,plain,(
% 3.87/0.88    ~r2_hidden(k7_setfam_1(sK0,sK1),k1_tarski(k1_tarski(k1_xboole_0)))),
% 3.87/0.88    inference(unit_resulting_resolution,[],[f59,f105])).
% 3.87/0.88  % SZS output end Proof for theBenchmark
% 3.87/0.88  % (22100)------------------------------
% 3.87/0.88  % (22100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.88  % (22100)Termination reason: Refutation
% 3.87/0.88  
% 3.87/0.88  % (22100)Memory used [KB]: 7931
% 3.87/0.88  % (22100)Time elapsed: 0.429 s
% 3.87/0.88  % (22100)------------------------------
% 3.87/0.88  % (22100)------------------------------
% 3.87/0.89  % (22074)Success in time 0.513 s
%------------------------------------------------------------------------------
