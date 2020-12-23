%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:57 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  109 (3149 expanded)
%              Number of leaves         :   18 ( 683 expanded)
%              Depth                    :   22
%              Number of atoms          :  266 (9109 expanded)
%              Number of equality atoms :   30 ( 473 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f936,f2429])).

fof(f2429,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f2420])).

fof(f2420,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f53,f2388,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2388,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f2052,f2369])).

fof(f2369,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f53,f1235,f1337])).

fof(f1337,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f1284,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1284,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1283,f1197])).

fof(f1197,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f1169,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f1169,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f1160,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f1160,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f1145,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1145,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f72,f953,f71,f1023,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f1023,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f751,f952])).

fof(f952,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f951,f79])).

fof(f79,plain,(
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

fof(f951,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f143,f700])).

fof(f700,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f284,f285,f100,f286,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f286,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f44,f45,f99,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f99,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f51])).

fof(f46,plain,(
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

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f100,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f285,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f44,f45,f99,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f284,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f44,f45,f99,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_1
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f751,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f287,f700])).

fof(f287,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f65])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f953,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f44,f952])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1283,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1200,f1197])).

fof(f1200,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl6_1 ),
    inference(resolution,[],[f1169,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1235,plain,
    ( r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1063,f1197])).

fof(f1063,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f914,f952])).

fof(f914,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f837,f79])).

fof(f837,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f701,f700])).

fof(f701,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f286,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2052,plain,
    ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f2051,f79])).

fof(f2051,plain,
    ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f1214,f1203,f1215,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f1215,plain,
    ( v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1022,f1197])).

fof(f1022,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f749,f952])).

fof(f749,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f285,f700])).

fof(f1203,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1010,f1197])).

fof(f1010,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f707,f952])).

fof(f707,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f100,f700])).

fof(f1214,plain,
    ( v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1021,f1197])).

fof(f1021,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f748,f952])).

fof(f748,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f284,f700])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f936,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f72,f71,f859,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f859,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2 ),
    inference(forward_demodulation,[],[f737,f79])).

fof(f737,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl6_2 ),
    inference(backward_demodulation,[],[f217,f700])).

fof(f217,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f149,f65])).

fof(f149,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f147,f51])).

fof(f147,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f148,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f98,f145,f141])).

fof(f98,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f90,f75])).

fof(f90,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (7642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (7649)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (7643)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (7638)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (7654)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (7661)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (7653)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (7666)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (7658)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (7641)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (7651)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (7639)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (7644)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (7645)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.55  % (7640)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.55  % (7667)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (7657)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (7648)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (7646)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (7647)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.55  % (7662)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (7659)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (7652)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (7665)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.56  % (7655)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.56  % (7664)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.56  % (7650)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.56  % (7656)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.57  % (7660)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.57  % (7663)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.62  % (7642)Refutation found. Thanks to Tanya!
% 1.53/0.62  % SZS status Theorem for theBenchmark
% 1.53/0.62  % SZS output start Proof for theBenchmark
% 1.53/0.62  fof(f2430,plain,(
% 1.53/0.62    $false),
% 1.53/0.62    inference(avatar_sat_refutation,[],[f148,f936,f2429])).
% 1.53/0.62  fof(f2429,plain,(
% 1.53/0.62    ~spl6_1),
% 1.53/0.62    inference(avatar_contradiction_clause,[],[f2420])).
% 1.53/0.62  fof(f2420,plain,(
% 1.53/0.62    $false | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f53,f2388,f48])).
% 1.53/0.62  fof(f48,plain,(
% 1.53/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f11])).
% 1.53/0.62  fof(f11,axiom,(
% 1.53/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.53/0.62  fof(f2388,plain,(
% 1.53/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_1),
% 1.53/0.62    inference(backward_demodulation,[],[f2052,f2369])).
% 1.53/0.62  fof(f2369,plain,(
% 1.53/0.62    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f53,f1235,f1337])).
% 1.53/0.62  fof(f1337,plain,(
% 1.53/0.62    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2)) ) | ~spl6_1),
% 1.53/0.62    inference(resolution,[],[f1284,f47])).
% 1.53/0.62  fof(f47,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f28])).
% 1.53/0.62  fof(f28,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.62    inference(flattening,[],[f27])).
% 1.53/0.62  fof(f27,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.62    inference(ennf_transformation,[],[f5])).
% 1.53/0.62  fof(f5,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.53/0.62  fof(f1284,plain,(
% 1.53/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl6_1),
% 1.53/0.62    inference(forward_demodulation,[],[f1283,f1197])).
% 1.53/0.62  fof(f1197,plain,(
% 1.53/0.62    k1_xboole_0 = sK0 | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f1169,f69])).
% 1.53/0.62  fof(f69,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f42])).
% 1.53/0.62  fof(f42,plain,(
% 1.53/0.62    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.53/0.62    inference(ennf_transformation,[],[f8])).
% 1.53/0.62  fof(f8,axiom,(
% 1.53/0.62    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.53/0.62  fof(f1169,plain,(
% 1.53/0.62    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f1160,f51])).
% 1.53/0.62  fof(f51,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f29])).
% 1.53/0.62  fof(f29,plain,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.62    inference(ennf_transformation,[],[f2])).
% 1.53/0.62  fof(f2,axiom,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.62  fof(f1160,plain,(
% 1.53/0.62    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f1145,f65])).
% 1.53/0.62  fof(f65,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f1])).
% 1.53/0.62  fof(f1,axiom,(
% 1.53/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.53/0.62  fof(f1145,plain,(
% 1.53/0.62    v1_xboole_0(sK0) | ~spl6_1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f72,f953,f71,f1023,f60])).
% 1.53/0.62  fof(f60,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~v1_xboole_0(X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f37])).
% 1.53/0.62  fof(f37,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.53/0.62    inference(flattening,[],[f36])).
% 1.53/0.62  fof(f36,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.53/0.62    inference(ennf_transformation,[],[f19])).
% 1.53/0.62  fof(f19,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).
% 1.53/0.62  fof(f1023,plain,(
% 1.53/0.62    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 1.53/0.62    inference(backward_demodulation,[],[f751,f952])).
% 1.53/0.62  fof(f952,plain,(
% 1.53/0.62    k1_xboole_0 = sK2 | ~spl6_1),
% 1.53/0.62    inference(forward_demodulation,[],[f951,f79])).
% 1.53/0.62  fof(f79,plain,(
% 1.53/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.53/0.62    inference(equality_resolution,[],[f68])).
% 1.53/0.62  fof(f68,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f7])).
% 1.53/0.62  fof(f7,axiom,(
% 1.53/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.53/0.62  fof(f951,plain,(
% 1.53/0.62    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~spl6_1),
% 1.53/0.62    inference(forward_demodulation,[],[f143,f700])).
% 1.53/0.62  fof(f700,plain,(
% 1.53/0.62    k1_xboole_0 = sK1),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f284,f285,f100,f286,f54])).
% 1.53/0.62  fof(f54,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f31])).
% 1.53/0.62  fof(f31,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.62    inference(flattening,[],[f30])).
% 1.53/0.62  fof(f30,plain,(
% 1.53/0.62    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.62    inference(ennf_transformation,[],[f20])).
% 1.53/0.62  fof(f20,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 1.53/0.62  fof(f286,plain,(
% 1.53/0.62    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f44,f45,f99,f59])).
% 1.53/0.62  fof(f59,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f35])).
% 1.53/0.62  fof(f35,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.53/0.62    inference(flattening,[],[f34])).
% 1.53/0.62  fof(f34,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.53/0.62    inference(ennf_transformation,[],[f22])).
% 1.53/0.62  fof(f22,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.53/0.62  fof(f99,plain,(
% 1.53/0.62    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f46,f51])).
% 1.53/0.62  fof(f46,plain,(
% 1.53/0.62    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.53/0.62    inference(cnf_transformation,[],[f26])).
% 1.53/0.62  fof(f26,plain,(
% 1.53/0.62    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.53/0.62    inference(flattening,[],[f25])).
% 1.53/0.62  fof(f25,plain,(
% 1.53/0.62    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.53/0.62    inference(ennf_transformation,[],[f24])).
% 1.53/0.62  fof(f24,negated_conjecture,(
% 1.53/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.53/0.62    inference(negated_conjecture,[],[f23])).
% 1.53/0.62  fof(f23,conjecture,(
% 1.53/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).
% 1.53/0.62  fof(f45,plain,(
% 1.53/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.62    inference(cnf_transformation,[],[f26])).
% 1.53/0.62  fof(f44,plain,(
% 1.53/0.62    v1_funct_1(sK2)),
% 1.53/0.62    inference(cnf_transformation,[],[f26])).
% 1.53/0.62  fof(f100,plain,(
% 1.53/0.62    ~r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f46,f52])).
% 1.53/0.62  fof(f52,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f29])).
% 1.53/0.62  fof(f285,plain,(
% 1.53/0.62    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f44,f45,f99,f58])).
% 1.53/0.62  fof(f58,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f35])).
% 1.53/0.62  fof(f284,plain,(
% 1.53/0.62    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f44,f45,f99,f57])).
% 1.53/0.62  fof(f57,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f35])).
% 1.53/0.62  fof(f143,plain,(
% 1.53/0.62    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_1),
% 1.53/0.62    inference(avatar_component_clause,[],[f141])).
% 1.53/0.62  fof(f141,plain,(
% 1.53/0.62    spl6_1 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.53/0.62  fof(f751,plain,(
% 1.53/0.62    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2))),
% 1.53/0.62    inference(backward_demodulation,[],[f287,f700])).
% 1.53/0.62  fof(f287,plain,(
% 1.53/0.62    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 1.53/0.62    inference(unit_resulting_resolution,[],[f99,f65])).
% 1.53/0.62  fof(f71,plain,(
% 1.53/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f10])).
% 1.53/0.62  fof(f10,axiom,(
% 1.53/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.53/0.62  fof(f953,plain,(
% 1.53/0.62    v1_funct_1(k1_xboole_0) | ~spl6_1),
% 1.53/0.62    inference(backward_demodulation,[],[f44,f952])).
% 1.53/0.62  fof(f72,plain,(
% 1.53/0.62    v1_xboole_0(k1_xboole_0)),
% 1.53/0.62    inference(cnf_transformation,[],[f3])).
% 1.53/0.62  fof(f3,axiom,(
% 1.53/0.62    v1_xboole_0(k1_xboole_0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.53/0.62  fof(f1283,plain,(
% 1.53/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | sK0 = X0) ) | ~spl6_1),
% 1.53/0.62    inference(forward_demodulation,[],[f1200,f1197])).
% 1.53/0.62  fof(f1200,plain,(
% 1.53/0.62    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl6_1),
% 1.53/0.62    inference(resolution,[],[f1169,f75])).
% 1.53/0.62  fof(f75,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.53/0.62    inference(cnf_transformation,[],[f4])).
% 1.53/0.62  fof(f4,axiom,(
% 1.53/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.63  fof(f1235,plain,(
% 1.53/0.63    r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f1063,f1197])).
% 1.53/0.63  fof(f1063,plain,(
% 1.53/0.63    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f914,f952])).
% 1.53/0.63  fof(f914,plain,(
% 1.53/0.63    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.53/0.63    inference(forward_demodulation,[],[f837,f79])).
% 1.53/0.63  fof(f837,plain,(
% 1.53/0.63    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.53/0.63    inference(backward_demodulation,[],[f701,f700])).
% 1.53/0.63  fof(f701,plain,(
% 1.53/0.63    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f286,f49])).
% 1.53/0.63  fof(f49,plain,(
% 1.53/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f11])).
% 1.53/0.63  fof(f2052,plain,(
% 1.53/0.63    ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl6_1),
% 1.53/0.63    inference(forward_demodulation,[],[f2051,f79])).
% 1.53/0.63  fof(f2051,plain,(
% 1.53/0.63    ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_1),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f1214,f1203,f1215,f56])).
% 1.53/0.63  fof(f56,plain,(
% 1.53/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | r2_hidden(X1,k1_funct_2(X0,X0))) )),
% 1.53/0.63    inference(cnf_transformation,[],[f33])).
% 1.53/0.63  fof(f33,plain,(
% 1.53/0.63    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.63    inference(flattening,[],[f32])).
% 1.53/0.63  fof(f32,plain,(
% 1.53/0.63    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.63    inference(ennf_transformation,[],[f21])).
% 1.53/0.63  fof(f21,axiom,(
% 1.53/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).
% 1.53/0.63  fof(f1215,plain,(
% 1.53/0.63    v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f1022,f1197])).
% 1.53/0.63  fof(f1022,plain,(
% 1.53/0.63    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f749,f952])).
% 1.53/0.63  fof(f749,plain,(
% 1.53/0.63    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0)),
% 1.53/0.63    inference(backward_demodulation,[],[f285,f700])).
% 1.53/0.63  fof(f1203,plain,(
% 1.53/0.63    ~r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f1010,f1197])).
% 1.53/0.63  fof(f1010,plain,(
% 1.53/0.63    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f707,f952])).
% 1.53/0.63  fof(f707,plain,(
% 1.53/0.63    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 1.53/0.63    inference(backward_demodulation,[],[f100,f700])).
% 1.53/0.63  fof(f1214,plain,(
% 1.53/0.63    v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f1021,f1197])).
% 1.53/0.63  fof(f1021,plain,(
% 1.53/0.63    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))) | ~spl6_1),
% 1.53/0.63    inference(backward_demodulation,[],[f748,f952])).
% 1.53/0.63  fof(f748,plain,(
% 1.53/0.63    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)))),
% 1.53/0.63    inference(backward_demodulation,[],[f284,f700])).
% 1.53/0.63  fof(f53,plain,(
% 1.53/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f6])).
% 1.53/0.63  fof(f6,axiom,(
% 1.53/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.63  fof(f936,plain,(
% 1.53/0.63    spl6_2),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f926])).
% 1.53/0.63  fof(f926,plain,(
% 1.53/0.63    $false | spl6_2),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f72,f71,f859,f61])).
% 1.53/0.63  fof(f61,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f38])).
% 1.53/0.63  fof(f38,plain,(
% 1.53/0.63    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.53/0.63    inference(ennf_transformation,[],[f16])).
% 1.53/0.63  fof(f16,axiom,(
% 1.53/0.63    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.53/0.63  fof(f859,plain,(
% 1.53/0.63    ~v1_xboole_0(k1_xboole_0) | spl6_2),
% 1.53/0.63    inference(forward_demodulation,[],[f737,f79])).
% 1.53/0.63  fof(f737,plain,(
% 1.53/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | spl6_2),
% 1.53/0.63    inference(backward_demodulation,[],[f217,f700])).
% 1.53/0.63  fof(f217,plain,(
% 1.53/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_2),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f149,f65])).
% 1.53/0.63  fof(f149,plain,(
% 1.53/0.63    r2_hidden(sK3(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1)) | spl6_2),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f147,f51])).
% 1.53/0.63  fof(f147,plain,(
% 1.53/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl6_2),
% 1.53/0.63    inference(avatar_component_clause,[],[f145])).
% 1.53/0.63  fof(f145,plain,(
% 1.53/0.63    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.53/0.63  fof(f148,plain,(
% 1.53/0.63    spl6_1 | ~spl6_2),
% 1.53/0.63    inference(avatar_split_clause,[],[f98,f145,f141])).
% 1.53/0.63  fof(f98,plain,(
% 1.53/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.53/0.63    inference(resolution,[],[f90,f75])).
% 1.53/0.63  fof(f90,plain,(
% 1.53/0.63    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.53/0.63    inference(unit_resulting_resolution,[],[f45,f49])).
% 1.53/0.63  % SZS output end Proof for theBenchmark
% 1.53/0.63  % (7642)------------------------------
% 1.53/0.63  % (7642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.63  % (7642)Termination reason: Refutation
% 1.53/0.63  
% 1.53/0.63  % (7642)Memory used [KB]: 6908
% 1.53/0.63  % (7642)Time elapsed: 0.195 s
% 1.53/0.63  % (7642)------------------------------
% 1.53/0.63  % (7642)------------------------------
% 2.00/0.65  % (7637)Success in time 0.283 s
%------------------------------------------------------------------------------
