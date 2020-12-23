%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:57 EST 2020

% Result     : Theorem 3.09s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  128 (8087 expanded)
%              Number of leaves         :   15 (1765 expanded)
%              Depth                    :   24
%              Number of atoms          :  338 (23531 expanded)
%              Number of equality atoms :   34 (1226 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f715,f4664,f5770])).

fof(f5770,plain,
    ( ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f5757])).

fof(f5757,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f65,f65,f5739,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f5739,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f5360,f5707])).

fof(f5707,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4786,f5050])).

fof(f5050,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_1 ),
    inference(resolution,[],[f4714,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f4714,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_1 ),
    inference(resolution,[],[f4695,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4695,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f1789,f43])).

fof(f1789,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f64,f1211,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f1211,plain,
    ( v1_xboole_0(k5_partfun1(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),sK0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f1186,f720,f64,f1191,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f1191,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f65,f720,f64,f1186,f53])).

fof(f720,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f36,f719])).

fof(f719,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f718,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f718,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f103,f500])).

fof(f500,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f212,f213,f86,f214,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f214,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f36,f37,f85,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f85,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f43])).

fof(f38,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f213,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f36,f37,f85,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f212,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f36,f37,f85,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_1
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f1186,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f66,f759])).

fof(f759,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f579,f719])).

fof(f579,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f431,f500])).

fof(f431,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f219,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f85,f56])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4786,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f1424,f4739])).

fof(f4739,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4695,f4722,f47])).

fof(f4722,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4677,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4677,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f1191,f205,f57])).

fof(f205,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1424,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f65,f767,f56])).

fof(f767,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f614,f719])).

fof(f614,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f524,f69])).

fof(f524,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f214,f500])).

fof(f5360,plain,
    ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f5359,f4981])).

fof(f4981,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4695,f4964,f47])).

fof(f4964,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4681,f41])).

fof(f4681,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f205,f205,f57])).

fof(f5359,plain,
    ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f5358,f69])).

fof(f5358,plain,
    ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f4745,f4742,f4746,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4746,plain,
    ( v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f751,f4739])).

fof(f751,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f523,f719])).

fof(f523,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f213,f500])).

fof(f4742,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f747,f4739])).

fof(f747,plain,
    ( ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f508,f719])).

fof(f508,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f86,f500])).

fof(f4745,plain,
    ( v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f750,f4739])).

fof(f750,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f522,f719])).

fof(f522,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f212,f500])).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4664,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f4654])).

fof(f4654,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f720,f4134,f64,f4133,f68])).

fof(f4133,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | spl4_7 ),
    inference(backward_demodulation,[],[f2109,f3907])).

fof(f3907,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f66,f1191,f3869])).

fof(f3869,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f1850,f40])).

fof(f1850,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_xboole_0(X1) )
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f911,f56])).

fof(f911,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f894,f43])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f868,f47])).

fof(f868,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f860,f43])).

fof(f860,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f64,f803,f56])).

fof(f803,plain,
    ( v1_xboole_0(k5_partfun1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f206,f65,f64,f720,f53])).

fof(f206,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f2109,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0))
    | ~ spl4_1
    | spl4_7 ),
    inference(backward_demodulation,[],[f747,f2103])).

fof(f2103,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f868,f775,f47])).

fof(f775,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f665,f719])).

fof(f665,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f599,f69])).

fof(f599,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f501,f500])).

fof(f501,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f214,f41])).

fof(f4134,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_7 ),
    inference(backward_demodulation,[],[f2111,f3907])).

fof(f2111,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_1
    | spl4_7 ),
    inference(backward_demodulation,[],[f751,f2103])).

fof(f715,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f604,f41])).

fof(f604,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl4_2 ),
    inference(forward_demodulation,[],[f512,f69])).

fof(f512,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | spl4_2 ),
    inference(backward_demodulation,[],[f107,f500])).

fof(f107,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f105,f101])).

fof(f84,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f77,f47])).

fof(f77,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (28579)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (28571)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28568)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (28566)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28567)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (28569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (28570)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (28588)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (28574)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (28565)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (28575)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (28584)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (28576)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (28592)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28577)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28589)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28591)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (28594)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (28572)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (28596)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (28585)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.56  % (28595)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.56  % (28581)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (28587)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (28586)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.56  % (28578)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (28573)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.57  % (28582)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.57  % (28590)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.19/0.68  % (28592)Refutation not found, incomplete strategy% (28592)------------------------------
% 2.19/0.68  % (28592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (28592)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.69  
% 2.19/0.69  % (28592)Memory used [KB]: 11129
% 2.19/0.69  % (28592)Time elapsed: 0.269 s
% 2.19/0.69  % (28592)------------------------------
% 2.19/0.69  % (28592)------------------------------
% 3.09/0.79  % (28569)Refutation found. Thanks to Tanya!
% 3.09/0.79  % SZS status Theorem for theBenchmark
% 3.09/0.79  % SZS output start Proof for theBenchmark
% 3.09/0.79  fof(f5776,plain,(
% 3.09/0.79    $false),
% 3.09/0.79    inference(avatar_sat_refutation,[],[f108,f715,f4664,f5770])).
% 3.09/0.79  fof(f5770,plain,(
% 3.09/0.79    ~spl4_1 | ~spl4_7),
% 3.09/0.79    inference(avatar_contradiction_clause,[],[f5757])).
% 3.09/0.79  fof(f5757,plain,(
% 3.09/0.79    $false | (~spl4_1 | ~spl4_7)),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f65,f65,f5739,f57])).
% 3.09/0.79  fof(f57,plain,(
% 3.09/0.79    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f35])).
% 3.09/0.79  fof(f35,plain,(
% 3.09/0.79    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.09/0.79    inference(ennf_transformation,[],[f6])).
% 3.09/0.79  fof(f6,axiom,(
% 3.09/0.79    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.09/0.79  fof(f5739,plain,(
% 3.09/0.79    ~m1_subset_1(k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_7)),
% 3.09/0.79    inference(backward_demodulation,[],[f5360,f5707])).
% 3.09/0.79  fof(f5707,plain,(
% 3.09/0.79    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl4_1 | ~spl4_7)),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f4786,f5050])).
% 3.09/0.79  fof(f5050,plain,(
% 3.09/0.79    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | ~spl4_1),
% 3.09/0.79    inference(resolution,[],[f4714,f43])).
% 3.09/0.79  fof(f43,plain,(
% 3.09/0.79    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f24])).
% 3.09/0.79  fof(f24,plain,(
% 3.09/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.09/0.79    inference(ennf_transformation,[],[f1])).
% 3.09/0.79  fof(f1,axiom,(
% 3.09/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.09/0.79  fof(f4714,plain,(
% 3.09/0.79    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_1),
% 3.09/0.79    inference(resolution,[],[f4695,f47])).
% 3.09/0.79  fof(f47,plain,(
% 3.09/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.09/0.79    inference(cnf_transformation,[],[f3])).
% 3.09/0.79  fof(f3,axiom,(
% 3.09/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.09/0.79  fof(f4695,plain,(
% 3.09/0.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f1789,f43])).
% 3.09/0.79  fof(f1789,plain,(
% 3.09/0.79    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f64,f1211,f56])).
% 3.09/0.79  fof(f56,plain,(
% 3.09/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f34])).
% 3.09/0.79  fof(f34,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.09/0.79    inference(ennf_transformation,[],[f10])).
% 3.09/0.79  fof(f10,axiom,(
% 3.09/0.79    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 3.09/0.79  fof(f1211,plain,(
% 3.09/0.79    v1_xboole_0(k5_partfun1(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),sK0,k1_xboole_0)) | ~spl4_1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f1186,f720,f64,f1191,f53])).
% 3.09/0.79  fof(f53,plain,(
% 3.09/0.79    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~v1_xboole_0(X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f30])).
% 3.09/0.79  fof(f30,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.09/0.79    inference(flattening,[],[f29])).
% 3.09/0.79  fof(f29,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.09/0.79    inference(ennf_transformation,[],[f15])).
% 3.09/0.79  fof(f15,axiom,(
% 3.09/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).
% 3.09/0.79  fof(f1191,plain,(
% 3.09/0.79    v1_xboole_0(sK0) | ~spl4_1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f65,f720,f64,f1186,f53])).
% 3.09/0.79  fof(f720,plain,(
% 3.09/0.79    v1_funct_1(k1_xboole_0) | ~spl4_1),
% 3.09/0.79    inference(backward_demodulation,[],[f36,f719])).
% 3.09/0.79  fof(f719,plain,(
% 3.09/0.79    k1_xboole_0 = sK2 | ~spl4_1),
% 3.09/0.79    inference(forward_demodulation,[],[f718,f69])).
% 3.09/0.79  fof(f69,plain,(
% 3.09/0.79    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.09/0.79    inference(equality_resolution,[],[f63])).
% 3.09/0.79  fof(f63,plain,(
% 3.09/0.79    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f5])).
% 3.09/0.79  fof(f5,axiom,(
% 3.09/0.79    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.09/0.79  fof(f718,plain,(
% 3.09/0.79    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~spl4_1),
% 3.09/0.79    inference(forward_demodulation,[],[f103,f500])).
% 3.09/0.79  fof(f500,plain,(
% 3.09/0.79    k1_xboole_0 = sK1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f212,f213,f86,f214,f48])).
% 3.09/0.79  fof(f48,plain,(
% 3.09/0.79    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.09/0.79    inference(cnf_transformation,[],[f26])).
% 3.09/0.79  fof(f26,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.09/0.79    inference(flattening,[],[f25])).
% 3.09/0.79  fof(f25,plain,(
% 3.09/0.79    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.09/0.79    inference(ennf_transformation,[],[f16])).
% 3.09/0.79  fof(f16,axiom,(
% 3.09/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).
% 3.09/0.79  fof(f214,plain,(
% 3.09/0.79    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f36,f37,f85,f52])).
% 3.09/0.79  fof(f52,plain,(
% 3.09/0.79    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.79    inference(cnf_transformation,[],[f28])).
% 3.09/0.79  fof(f28,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.09/0.79    inference(flattening,[],[f27])).
% 3.09/0.79  fof(f27,plain,(
% 3.09/0.79    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.09/0.79    inference(ennf_transformation,[],[f17])).
% 3.09/0.79  fof(f17,axiom,(
% 3.09/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 3.09/0.79  fof(f85,plain,(
% 3.09/0.79    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f38,f43])).
% 3.09/0.79  fof(f38,plain,(
% 3.09/0.79    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 3.09/0.79    inference(cnf_transformation,[],[f21])).
% 3.09/0.79  fof(f21,plain,(
% 3.09/0.79    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.09/0.79    inference(flattening,[],[f20])).
% 3.09/0.79  fof(f20,plain,(
% 3.09/0.79    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.09/0.79    inference(ennf_transformation,[],[f19])).
% 3.09/0.79  fof(f19,negated_conjecture,(
% 3.09/0.79    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.09/0.79    inference(negated_conjecture,[],[f18])).
% 3.09/0.79  fof(f18,conjecture,(
% 3.09/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).
% 3.09/0.79  fof(f37,plain,(
% 3.09/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.09/0.79    inference(cnf_transformation,[],[f21])).
% 3.09/0.79  fof(f86,plain,(
% 3.09/0.79    ~r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f38,f44])).
% 3.09/0.79  fof(f44,plain,(
% 3.09/0.79    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f24])).
% 3.09/0.79  fof(f213,plain,(
% 3.09/0.79    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f36,f37,f85,f51])).
% 3.09/0.79  fof(f51,plain,(
% 3.09/0.79    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f28])).
% 3.09/0.79  fof(f212,plain,(
% 3.09/0.79    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f36,f37,f85,f50])).
% 3.09/0.79  fof(f50,plain,(
% 3.09/0.79    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f28])).
% 3.09/0.79  fof(f103,plain,(
% 3.09/0.79    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl4_1),
% 3.09/0.79    inference(avatar_component_clause,[],[f101])).
% 3.09/0.79  fof(f101,plain,(
% 3.09/0.79    spl4_1 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 3.09/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.09/0.79  fof(f36,plain,(
% 3.09/0.79    v1_funct_1(sK2)),
% 3.09/0.79    inference(cnf_transformation,[],[f21])).
% 3.09/0.79  fof(f1186,plain,(
% 3.09/0.79    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | ~spl4_1),
% 3.09/0.79    inference(unit_resulting_resolution,[],[f66,f759])).
% 3.09/0.79  fof(f759,plain,(
% 3.09/0.79    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),X0) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 3.09/0.79    inference(backward_demodulation,[],[f579,f719])).
% 3.09/0.79  fof(f579,plain,(
% 3.09/0.79    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | ~v1_xboole_0(X0)) )),
% 3.09/0.79    inference(backward_demodulation,[],[f431,f500])).
% 3.09/0.79  fof(f431,plain,(
% 3.09/0.79    ( ! [X0] : (~v1_xboole_0(X0) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 3.09/0.79    inference(resolution,[],[f219,f40])).
% 3.09/0.79  fof(f40,plain,(
% 3.09/0.79    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.09/0.79    inference(cnf_transformation,[],[f8])).
% 3.09/0.79  fof(f8,axiom,(
% 3.09/0.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.09/0.80  fof(f219,plain,(
% 3.09/0.80    ( ! [X0] : (~m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.09/0.80    inference(resolution,[],[f85,f56])).
% 3.09/0.80  fof(f66,plain,(
% 3.09/0.80    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/0.80    inference(equality_resolution,[],[f46])).
% 3.09/0.80  fof(f46,plain,(
% 3.09/0.80    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.09/0.80    inference(cnf_transformation,[],[f3])).
% 3.09/0.80  fof(f64,plain,(
% 3.09/0.80    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.09/0.80    inference(cnf_transformation,[],[f7])).
% 3.09/0.80  fof(f7,axiom,(
% 3.09/0.80    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.09/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.09/0.80  fof(f4786,plain,(
% 3.09/0.80    ( ! [X0] : (~r2_hidden(X0,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))) ) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f1424,f4739])).
% 3.09/0.80  fof(f4739,plain,(
% 3.09/0.80    k1_xboole_0 = sK0 | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f4695,f4722,f47])).
% 3.09/0.80  fof(f4722,plain,(
% 3.09/0.80    r1_tarski(sK0,k1_xboole_0) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f4677,f41])).
% 3.09/0.80  fof(f41,plain,(
% 3.09/0.80    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.09/0.80    inference(cnf_transformation,[],[f8])).
% 3.09/0.80  fof(f4677,plain,(
% 3.09/0.80    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f1191,f205,f57])).
% 3.09/0.80  fof(f205,plain,(
% 3.09/0.80    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~spl4_7),
% 3.09/0.80    inference(avatar_component_clause,[],[f204])).
% 3.09/0.80  fof(f204,plain,(
% 3.09/0.80    spl4_7 <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 3.09/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.09/0.80  fof(f1424,plain,(
% 3.09/0.80    ( ! [X0] : (~r2_hidden(X0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))) ) | ~spl4_1),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f65,f767,f56])).
% 3.09/0.80  fof(f767,plain,(
% 3.09/0.80    m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl4_1),
% 3.09/0.80    inference(backward_demodulation,[],[f614,f719])).
% 3.09/0.80  fof(f614,plain,(
% 3.09/0.80    m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 3.09/0.80    inference(forward_demodulation,[],[f524,f69])).
% 3.09/0.80  fof(f524,plain,(
% 3.09/0.80    m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 3.09/0.80    inference(backward_demodulation,[],[f214,f500])).
% 3.09/0.80  fof(f5360,plain,(
% 3.09/0.80    ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(forward_demodulation,[],[f5359,f4981])).
% 3.09/0.80  fof(f4981,plain,(
% 3.09/0.80    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f4695,f4964,f47])).
% 3.09/0.80  fof(f4964,plain,(
% 3.09/0.80    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | ~spl4_7),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f4681,f41])).
% 3.09/0.80  fof(f4681,plain,(
% 3.09/0.80    m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_7),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f205,f205,f57])).
% 3.09/0.80  fof(f5359,plain,(
% 3.09/0.80    ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(forward_demodulation,[],[f5358,f69])).
% 3.09/0.80  fof(f5358,plain,(
% 3.09/0.80    ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f4745,f4742,f4746,f68])).
% 3.09/0.80  fof(f68,plain,(
% 3.09/0.80    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))) )),
% 3.09/0.80    inference(equality_resolution,[],[f49])).
% 3.09/0.80  fof(f49,plain,(
% 3.09/0.80    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.09/0.80    inference(cnf_transformation,[],[f26])).
% 3.09/0.80  fof(f4746,plain,(
% 3.09/0.80    v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f751,f4739])).
% 3.09/0.80  fof(f751,plain,(
% 3.09/0.80    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0) | ~spl4_1),
% 3.09/0.80    inference(backward_demodulation,[],[f523,f719])).
% 3.09/0.80  fof(f523,plain,(
% 3.09/0.80    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),sK0,k1_xboole_0)),
% 3.09/0.80    inference(backward_demodulation,[],[f213,f500])).
% 3.09/0.80  fof(f4742,plain,(
% 3.09/0.80    ~r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f747,f4739])).
% 3.09/0.80  fof(f747,plain,(
% 3.09/0.80    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) | ~spl4_1),
% 3.09/0.80    inference(backward_demodulation,[],[f508,f719])).
% 3.09/0.80  fof(f508,plain,(
% 3.09/0.80    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 3.09/0.80    inference(backward_demodulation,[],[f86,f500])).
% 3.09/0.80  fof(f4745,plain,(
% 3.09/0.80    v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f750,f4739])).
% 3.09/0.80  fof(f750,plain,(
% 3.09/0.80    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))) | ~spl4_1),
% 3.09/0.80    inference(backward_demodulation,[],[f522,f719])).
% 3.09/0.80  fof(f522,plain,(
% 3.09/0.80    v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)))),
% 3.09/0.80    inference(backward_demodulation,[],[f212,f500])).
% 3.09/0.80  fof(f65,plain,(
% 3.09/0.80    v1_xboole_0(k1_xboole_0)),
% 3.09/0.80    inference(cnf_transformation,[],[f2])).
% 3.09/0.80  fof(f2,axiom,(
% 3.09/0.80    v1_xboole_0(k1_xboole_0)),
% 3.09/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.09/0.80  fof(f4664,plain,(
% 3.09/0.80    ~spl4_1 | spl4_7),
% 3.09/0.80    inference(avatar_contradiction_clause,[],[f4654])).
% 3.09/0.80  fof(f4654,plain,(
% 3.09/0.80    $false | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f720,f4134,f64,f4133,f68])).
% 3.09/0.80  fof(f4133,plain,(
% 3.09/0.80    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f2109,f3907])).
% 3.09/0.80  fof(f3907,plain,(
% 3.09/0.80    k1_xboole_0 = sK0 | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f66,f1191,f3869])).
% 3.09/0.80  fof(f3869,plain,(
% 3.09/0.80    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(resolution,[],[f1850,f40])).
% 3.09/0.80  fof(f1850,plain,(
% 3.09/0.80    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0 | ~v1_xboole_0(X1)) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(resolution,[],[f911,f56])).
% 3.09/0.80  fof(f911,plain,(
% 3.09/0.80    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(resolution,[],[f894,f43])).
% 3.09/0.80  fof(f894,plain,(
% 3.09/0.80    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(resolution,[],[f868,f47])).
% 3.09/0.80  fof(f868,plain,(
% 3.09/0.80    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f860,f43])).
% 3.09/0.80  fof(f860,plain,(
% 3.09/0.80    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f64,f803,f56])).
% 3.09/0.80  fof(f803,plain,(
% 3.09/0.80    v1_xboole_0(k5_partfun1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f206,f65,f64,f720,f53])).
% 3.09/0.80  fof(f206,plain,(
% 3.09/0.80    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | spl4_7),
% 3.09/0.80    inference(avatar_component_clause,[],[f204])).
% 3.09/0.80  fof(f2109,plain,(
% 3.09/0.80    ~r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0)) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f747,f2103])).
% 3.09/0.80  fof(f2103,plain,(
% 3.09/0.80    k1_xboole_0 = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f868,f775,f47])).
% 3.09/0.80  fof(f775,plain,(
% 3.09/0.80    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl4_1),
% 3.09/0.80    inference(backward_demodulation,[],[f665,f719])).
% 3.09/0.80  fof(f665,plain,(
% 3.09/0.80    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 3.09/0.80    inference(forward_demodulation,[],[f599,f69])).
% 3.09/0.80  fof(f599,plain,(
% 3.09/0.80    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0))),
% 3.09/0.80    inference(backward_demodulation,[],[f501,f500])).
% 3.09/0.80  fof(f501,plain,(
% 3.09/0.80    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f214,f41])).
% 3.09/0.80  fof(f4134,plain,(
% 3.09/0.80    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f2111,f3907])).
% 3.09/0.80  fof(f2111,plain,(
% 3.09/0.80    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl4_1 | spl4_7)),
% 3.09/0.80    inference(backward_demodulation,[],[f751,f2103])).
% 3.09/0.80  fof(f715,plain,(
% 3.09/0.80    spl4_2),
% 3.09/0.80    inference(avatar_contradiction_clause,[],[f708])).
% 3.09/0.80  fof(f708,plain,(
% 3.09/0.80    $false | spl4_2),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f64,f604,f41])).
% 3.09/0.80  fof(f604,plain,(
% 3.09/0.80    ~r1_tarski(k1_xboole_0,sK2) | spl4_2),
% 3.09/0.80    inference(forward_demodulation,[],[f512,f69])).
% 3.09/0.80  fof(f512,plain,(
% 3.09/0.80    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | spl4_2),
% 3.09/0.80    inference(backward_demodulation,[],[f107,f500])).
% 3.09/0.80  fof(f107,plain,(
% 3.09/0.80    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl4_2),
% 3.09/0.80    inference(avatar_component_clause,[],[f105])).
% 3.09/0.80  fof(f105,plain,(
% 3.09/0.80    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 3.09/0.80    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.09/0.80  fof(f108,plain,(
% 3.09/0.80    spl4_1 | ~spl4_2),
% 3.09/0.80    inference(avatar_split_clause,[],[f84,f105,f101])).
% 3.09/0.80  fof(f84,plain,(
% 3.09/0.80    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 3.09/0.80    inference(resolution,[],[f77,f47])).
% 3.09/0.80  fof(f77,plain,(
% 3.09/0.80    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 3.09/0.80    inference(unit_resulting_resolution,[],[f37,f41])).
% 3.09/0.80  % SZS output end Proof for theBenchmark
% 3.09/0.80  % (28569)------------------------------
% 3.09/0.80  % (28569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.80  % (28569)Termination reason: Refutation
% 3.09/0.80  
% 3.09/0.80  % (28569)Memory used [KB]: 8187
% 3.09/0.80  % (28569)Time elapsed: 0.372 s
% 3.09/0.80  % (28569)------------------------------
% 3.09/0.80  % (28569)------------------------------
% 3.09/0.80  % (28562)Success in time 0.429 s
%------------------------------------------------------------------------------
