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
% DateTime   : Thu Dec  3 13:06:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 (2487 expanded)
%              Number of leaves         :   17 ( 540 expanded)
%              Depth                    :   22
%              Number of atoms          :  247 (7183 expanded)
%              Number of equality atoms :   28 ( 388 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1045,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f522,f1041])).

fof(f1041,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f871,f74,f978,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f978,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f691,f964])).

fof(f964,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f56,f706,f55])).

fof(f55,plain,(
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

fof(f706,plain,
    ( r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f616,f684])).

fof(f684,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f675,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f675,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f72,f534,f71,f579,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f579,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f400,f533])).

fof(f533,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f532,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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

fof(f532,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f116,f364])).

fof(f364,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f178,f179,f105,f180,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f180,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f104,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f104,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f179,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f43,f44,f104,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f104,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_1
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f400,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f181,f364])).

fof(f181,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f104,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f534,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f43,f533])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f616,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f503,f533])).

fof(f503,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f453,f77])).

fof(f453,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f365,f364])).

fof(f365,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f180,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f691,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f573,f684])).

fof(f573,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f376,f533])).

fof(f376,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f105,f364])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f871,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f534,f71,f840,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).

fof(f840,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f790,f825])).

fof(f825,plain,
    ( k1_xboole_0 = sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f56,f805,f55])).

fof(f805,plain,
    ( r1_tarski(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f797,f49])).

fof(f797,plain,
    ( m1_subset_1(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f791,f77])).

fof(f791,plain,
    ( m1_subset_1(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f534,f71,f699,f62])).

fof(f699,plain,
    ( r2_hidden(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f581,f684])).

fof(f581,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f415,f533])).

fof(f415,plain,(
    r2_hidden(sK4(k5_partfun1(sK0,k1_xboole_0,sK2)),k5_partfun1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f221,f364])).

fof(f221,plain,(
    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f181,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f790,plain,
    ( v1_funct_2(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f534,f71,f699,f61])).

fof(f522,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f72,f71,f468,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f468,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2 ),
    inference(forward_demodulation,[],[f386,f77])).

fof(f386,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl5_2 ),
    inference(backward_demodulation,[],[f136,f364])).

fof(f136,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f122,f66])).

fof(f122,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f120,f51])).

fof(f120,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f121,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f94,f118,f114])).

fof(f94,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f44,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:57:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (8267)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (8260)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (8283)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (8263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (8275)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (8259)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (8281)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (8282)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (8278)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (8264)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (8265)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (8274)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (8268)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (8285)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (8266)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (8269)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (8276)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (8261)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (8262)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (8277)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (8271)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (8261)Refutation not found, incomplete strategy% (8261)------------------------------
% 0.22/0.56  % (8261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8261)Memory used [KB]: 10746
% 0.22/0.56  % (8261)Time elapsed: 0.131 s
% 0.22/0.56  % (8261)------------------------------
% 0.22/0.56  % (8261)------------------------------
% 0.22/0.56  % (8272)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (8286)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (8279)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (8287)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (8284)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (8288)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (8281)Refutation not found, incomplete strategy% (8281)------------------------------
% 0.22/0.57  % (8281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8281)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8281)Memory used [KB]: 10746
% 0.22/0.57  % (8281)Time elapsed: 0.128 s
% 0.22/0.57  % (8281)------------------------------
% 0.22/0.57  % (8281)------------------------------
% 0.22/0.57  % (8273)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (8280)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.59  % (8263)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1045,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f121,f522,f1041])).
% 0.22/0.59  fof(f1041,plain,(
% 0.22/0.59    ~spl5_1),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1029])).
% 0.22/0.59  fof(f1029,plain,(
% 0.22/0.59    $false | ~spl5_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f871,f74,f978,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.59  fof(f978,plain,(
% 0.22/0.59    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f691,f964])).
% 0.22/0.59  fof(f964,plain,(
% 0.22/0.59    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f56,f706,f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f706,plain,(
% 0.22/0.59    r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f616,f684])).
% 0.22/0.59  fof(f684,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | ~spl5_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f675,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.59  fof(f675,plain,(
% 0.22/0.59    v1_xboole_0(sK0) | ~spl5_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f72,f534,f71,f579,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~v1_xboole_0(X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).
% 0.22/0.59  fof(f579,plain,(
% 0.22/0.59    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f400,f533])).
% 0.22/0.59  fof(f533,plain,(
% 0.22/0.59    k1_xboole_0 = sK2 | ~spl5_1),
% 0.22/0.59    inference(forward_demodulation,[],[f532,f77])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(equality_resolution,[],[f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.59  fof(f532,plain,(
% 0.22/0.59    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~spl5_1),
% 0.22/0.59    inference(forward_demodulation,[],[f116,f364])).
% 0.22/0.59  fof(f364,plain,(
% 0.22/0.59    k1_xboole_0 = sK1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f178,f179,f105,f180,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 0.22/0.59  fof(f180,plain,(
% 0.22/0.59    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f43,f44,f104,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 0.22/0.59  fof(f104,plain,(
% 0.22/0.59    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f45,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f24])).
% 0.22/0.59  fof(f24,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 0.22/0.59    inference(negated_conjecture,[],[f23])).
% 0.22/0.59  fof(f23,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    v1_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ~r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f45,f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f179,plain,(
% 0.22/0.59    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f43,f44,f104,f61])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f178,plain,(
% 0.22/0.59    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f43,f44,f104,f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f116,plain,(
% 0.22/0.59    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f114])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    spl5_1 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.59  fof(f400,plain,(
% 0.22/0.59    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2))),
% 0.22/0.59    inference(backward_demodulation,[],[f181,f364])).
% 0.22/0.59  fof(f181,plain,(
% 0.22/0.59    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f104,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.59  fof(f534,plain,(
% 0.22/0.59    v1_funct_1(k1_xboole_0) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f43,f533])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.59  fof(f616,plain,(
% 0.22/0.59    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f503,f533])).
% 0.22/0.59  fof(f503,plain,(
% 0.22/0.59    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.59    inference(forward_demodulation,[],[f453,f77])).
% 0.22/0.59  fof(f453,plain,(
% 0.22/0.59    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0))),
% 0.22/0.59    inference(backward_demodulation,[],[f365,f364])).
% 0.22/0.59  fof(f365,plain,(
% 0.22/0.59    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f180,f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.59  fof(f691,plain,(
% 0.22/0.59    ~r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f573,f684])).
% 0.22/0.59  fof(f573,plain,(
% 0.22/0.59    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(backward_demodulation,[],[f376,f533])).
% 0.22/0.59  fof(f376,plain,(
% 0.22/0.59    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 0.22/0.59    inference(backward_demodulation,[],[f105,f364])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f871,plain,(
% 0.22/0.59    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f534,f71,f840,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | r2_hidden(X1,k1_funct_2(X0,X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.59    inference(flattening,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).
% 0.22/0.59  fof(f840,plain,(
% 0.22/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_1),
% 0.22/0.60    inference(backward_demodulation,[],[f790,f825])).
% 0.22/0.60  fof(f825,plain,(
% 0.22/0.60    k1_xboole_0 = sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f56,f805,f55])).
% 0.22/0.60  fof(f805,plain,(
% 0.22/0.60    r1_tarski(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f797,f49])).
% 0.22/0.60  fof(f797,plain,(
% 0.22/0.60    m1_subset_1(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl5_1),
% 0.22/0.60    inference(forward_demodulation,[],[f791,f77])).
% 0.22/0.60  fof(f791,plain,(
% 0.22/0.60    m1_subset_1(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f534,f71,f699,f62])).
% 0.22/0.60  fof(f699,plain,(
% 0.22/0.60    r2_hidden(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.60    inference(backward_demodulation,[],[f581,f684])).
% 0.22/0.60  fof(f581,plain,(
% 0.22/0.60    r2_hidden(sK4(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | ~spl5_1),
% 0.22/0.60    inference(backward_demodulation,[],[f415,f533])).
% 0.22/0.60  fof(f415,plain,(
% 0.22/0.60    r2_hidden(sK4(k5_partfun1(sK0,k1_xboole_0,sK2)),k5_partfun1(sK0,k1_xboole_0,sK2))),
% 0.22/0.60    inference(backward_demodulation,[],[f221,f364])).
% 0.22/0.60  fof(f221,plain,(
% 0.22/0.60    r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f181,f65])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f790,plain,(
% 0.22/0.60    v1_funct_2(sK4(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0) | ~spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f534,f71,f699,f61])).
% 0.22/0.60  fof(f522,plain,(
% 0.22/0.60    spl5_2),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f516])).
% 0.22/0.60  fof(f516,plain,(
% 0.22/0.60    $false | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f72,f71,f468,f73])).
% 0.22/0.60  fof(f73,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f42])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,axiom,(
% 0.22/0.60    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.60  fof(f468,plain,(
% 0.22/0.60    ~v1_xboole_0(k1_xboole_0) | spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f386,f77])).
% 0.22/0.60  fof(f386,plain,(
% 0.22/0.60    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | spl5_2),
% 0.22/0.60    inference(backward_demodulation,[],[f136,f364])).
% 0.22/0.60  fof(f136,plain,(
% 0.22/0.60    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f122,f66])).
% 0.22/0.60  fof(f122,plain,(
% 0.22/0.60    r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f120,f51])).
% 0.22/0.60  fof(f120,plain,(
% 0.22/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl5_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f118])).
% 0.22/0.60  fof(f118,plain,(
% 0.22/0.60    spl5_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.60  fof(f121,plain,(
% 0.22/0.60    spl5_1 | ~spl5_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f94,f118,f114])).
% 0.22/0.60  fof(f94,plain,(
% 0.22/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.60    inference(resolution,[],[f89,f55])).
% 0.22/0.60  fof(f89,plain,(
% 0.22/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f44,f49])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (8263)------------------------------
% 0.22/0.60  % (8263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (8263)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (8263)Memory used [KB]: 6524
% 0.22/0.60  % (8263)Time elapsed: 0.148 s
% 0.22/0.60  % (8263)------------------------------
% 0.22/0.60  % (8263)------------------------------
% 0.22/0.60  % (8258)Success in time 0.224 s
%------------------------------------------------------------------------------
