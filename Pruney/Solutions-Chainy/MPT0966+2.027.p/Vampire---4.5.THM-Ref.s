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
% DateTime   : Thu Dec  3 13:00:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  138 (3864 expanded)
%              Number of leaves         :   19 ( 902 expanded)
%              Depth                    :   22
%              Number of atoms          :  388 (18276 expanded)
%              Number of equality atoms :   90 (5160 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f147,f179,f183,f412,f604,f633])).

fof(f633,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f468,f609,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f609,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(forward_demodulation,[],[f608,f532])).

fof(f532,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f474,f528])).

fof(f528,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f472,f504,f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f504,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f476,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f476,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f448,f447])).

fof(f447,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f444,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f444,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f48,f421,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f421,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f416,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f416,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f37,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f448,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f444,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f472,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f428,f447])).

fof(f428,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f415,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f415,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f36,f85])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f474,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f430,f447])).

fof(f430,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f419,f82])).

fof(f419,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f105,f85])).

fof(f105,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f37,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f608,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(forward_demodulation,[],[f607,f447])).

fof(f607,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f167,f82])).

fof(f167,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f103,f107,f138,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f138,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f107,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f38,f102])).

fof(f102,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f38,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f58,f37,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f468,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f421,f447])).

fof(f604,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f468,f583,f51])).

fof(f583,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(forward_demodulation,[],[f582,f536])).

fof(f536,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f525,f532])).

fof(f525,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f504,f67])).

fof(f582,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f476,f527,f44])).

fof(f44,plain,(
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

fof(f527,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f471,f504,f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f471,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f427,f447])).

fof(f427,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl7_1
    | spl7_4 ),
    inference(backward_demodulation,[],[f142,f82])).

fof(f142,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f412,plain,
    ( spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f363,f309,f364,f74])).

fof(f364,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f265,f346])).

fof(f346,plain,
    ( k1_xboole_0 = sK0
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f263,f309,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f263,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f209,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK3
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f230,f45])).

fof(f230,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f48,f215,f56])).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl7_2
    | spl7_4 ),
    inference(forward_demodulation,[],[f208,f69])).

fof(f208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f128,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK2
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f142,f128,f198,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f198,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl7_2 ),
    inference(forward_demodulation,[],[f192,f108])).

fof(f108,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl7_2 ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f86,f36,f37,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f67])).

fof(f192,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f128,f67])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl7_2 ),
    inference(forward_demodulation,[],[f125,f108])).

fof(f125,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(unit_resulting_resolution,[],[f103,f71,f107,f49])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f209,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f142,f202])).

fof(f265,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f212,f233])).

fof(f212,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f198,f202])).

fof(f309,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f273,f50])).

fof(f273,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f234,f233])).

fof(f234,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f230,f53])).

fof(f363,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f263,f346])).

fof(f183,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f35,f146])).

fof(f146,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f179,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f72,f170])).

fof(f170,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl7_2
    | spl7_3 ),
    inference(forward_demodulation,[],[f167,f108])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f147,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f33,f144,f140,f136])).

fof(f33,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f84,f80])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (27891)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (27899)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (27883)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (27881)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (27879)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (27877)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (27876)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (27882)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (27880)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (27902)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (27892)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (27901)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (27904)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (27905)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (27903)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (27890)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (27884)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (27894)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (27896)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (27897)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (27895)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (27898)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (27900)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (27886)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (27888)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (27886)Refutation not found, incomplete strategy% (27886)------------------------------
% 0.22/0.56  % (27886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27886)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27886)Memory used [KB]: 10746
% 0.22/0.56  % (27886)Time elapsed: 0.149 s
% 0.22/0.56  % (27886)------------------------------
% 0.22/0.56  % (27886)------------------------------
% 0.22/0.56  % (27889)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (27887)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (27878)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (27880)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f634,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f87,f147,f179,f183,f412,f604,f633])).
% 0.22/0.57  fof(f633,plain,(
% 0.22/0.57    ~spl7_1 | ~spl7_2 | spl7_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f624])).
% 0.22/0.57  fof(f624,plain,(
% 0.22/0.57    $false | (~spl7_1 | ~spl7_2 | spl7_3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f468,f609,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f609,plain,(
% 0.22/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2 | spl7_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f608,f532])).
% 0.22/0.57  fof(f532,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(backward_demodulation,[],[f474,f528])).
% 0.22/0.57  fof(f528,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f472,f504,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.57    inference(equality_resolution,[],[f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.57  fof(f504,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f476,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f476,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_2),
% 0.22/0.57    inference(backward_demodulation,[],[f448,f447])).
% 0.22/0.57  fof(f447,plain,(
% 0.22/0.57    k1_xboole_0 = sK3 | ~spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f444,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.57  fof(f444,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f48,f421,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.57  fof(f421,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 0.22/0.57    inference(forward_demodulation,[],[f416,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.57  fof(f416,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_2),
% 0.22/0.57    inference(backward_demodulation,[],[f37,f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl7_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f84])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.57    inference(flattening,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.57    inference(negated_conjecture,[],[f17])).
% 0.22/0.57  fof(f17,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.57  fof(f448,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f444,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f472,plain,(
% 0.22/0.57    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(backward_demodulation,[],[f428,f447])).
% 0.22/0.57  fof(f428,plain,(
% 0.22/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(backward_demodulation,[],[f415,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl7_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    spl7_1 <=> k1_xboole_0 = sK0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.57  fof(f415,plain,(
% 0.22/0.57    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_2),
% 0.22/0.57    inference(backward_demodulation,[],[f36,f85])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f474,plain,(
% 0.22/0.57    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(backward_demodulation,[],[f430,f447])).
% 0.22/0.57  fof(f430,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(backward_demodulation,[],[f419,f82])).
% 0.22/0.57  fof(f419,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl7_2),
% 0.22/0.57    inference(backward_demodulation,[],[f105,f85])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.57    inference(resolution,[],[f37,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.57  fof(f608,plain,(
% 0.22/0.57    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl7_1 | ~spl7_2 | spl7_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f607,f447])).
% 0.22/0.57  fof(f607,plain,(
% 0.22/0.57    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (~spl7_1 | spl7_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f167,f82])).
% 0.22/0.57  fof(f167,plain,(
% 0.22/0.57    ~r1_tarski(k1_relat_1(sK3),sK0) | spl7_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f103,f107,f138,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl7_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f136])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.57    inference(backward_demodulation,[],[f38,f102])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    v1_relat_1(sK3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f58,f37,f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.57  fof(f468,plain,(
% 0.22/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 0.22/0.57    inference(backward_demodulation,[],[f421,f447])).
% 0.22/0.57  fof(f604,plain,(
% 0.22/0.57    ~spl7_1 | ~spl7_2 | spl7_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f595])).
% 0.22/0.57  fof(f595,plain,(
% 0.22/0.57    $false | (~spl7_1 | ~spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f468,f583,f51])).
% 0.22/0.57  fof(f583,plain,(
% 0.22/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_1 | ~spl7_2 | spl7_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f582,f536])).
% 0.22/0.57  fof(f536,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl7_1 | ~spl7_2)),
% 0.22/0.57    inference(forward_demodulation,[],[f525,f532])).
% 0.22/0.57  fof(f525,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f504,f67])).
% 0.22/0.57  fof(f582,plain,(
% 0.22/0.57    ~r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0) | (~spl7_1 | ~spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f476,f527,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f527,plain,(
% 0.22/0.57    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl7_1 | ~spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f471,f504,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f471,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_1 | ~spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f427,f447])).
% 0.22/0.57  fof(f427,plain,(
% 0.22/0.57    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl7_1 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f142,f82])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ~v1_funct_2(sK3,sK0,sK2) | spl7_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f140])).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    spl7_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.57  fof(f412,plain,(
% 0.22/0.57    spl7_2 | spl7_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.57  fof(f407,plain,(
% 0.22/0.57    $false | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f363,f309,f364,f74])).
% 0.22/0.57  fof(f364,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f265,f346])).
% 0.22/0.57  fof(f346,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f263,f309,f77])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f263,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f209,f233])).
% 0.22/0.57  fof(f233,plain,(
% 0.22/0.57    k1_xboole_0 = sK3 | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f230,f45])).
% 0.22/0.57  fof(f230,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f48,f215,f56])).
% 0.22/0.57  fof(f215,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f208,f69])).
% 0.22/0.57  fof(f208,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f128,f202])).
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    k1_xboole_0 = sK2 | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f142,f128,f198,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f198,plain,(
% 0.22/0.57    sK0 = k1_relset_1(sK0,sK2,sK3) | spl7_2),
% 0.22/0.57    inference(forward_demodulation,[],[f192,f108])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    sK0 = k1_relat_1(sK3) | spl7_2),
% 0.22/0.57    inference(forward_demodulation,[],[f100,f101])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f86,f36,f37,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl7_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f84])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f67])).
% 0.22/0.57  fof(f192,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl7_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f128,f67])).
% 0.22/0.57  fof(f128,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl7_2),
% 0.22/0.57    inference(forward_demodulation,[],[f125,f108])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f103,f71,f107,f49])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f209,plain,(
% 0.22/0.57    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f142,f202])).
% 0.22/0.57  fof(f265,plain,(
% 0.22/0.57    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f212,f233])).
% 0.22/0.57  fof(f212,plain,(
% 0.22/0.57    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f198,f202])).
% 0.22/0.57  fof(f309,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f273,f50])).
% 0.22/0.57  fof(f273,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f234,f233])).
% 0.22/0.57  fof(f234,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(sK3,X0)) ) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f230,f53])).
% 0.22/0.57  fof(f363,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.22/0.57    inference(backward_demodulation,[],[f263,f346])).
% 0.22/0.57  fof(f183,plain,(
% 0.22/0.57    spl7_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.57  fof(f180,plain,(
% 0.22/0.57    $false | spl7_5),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f35,f146])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    ~v1_funct_1(sK3) | spl7_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f144])).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    spl7_5 <=> v1_funct_1(sK3)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    v1_funct_1(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f179,plain,(
% 0.22/0.57    spl7_2 | spl7_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.57  fof(f171,plain,(
% 0.22/0.57    $false | (spl7_2 | spl7_3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f170])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK0) | (spl7_2 | spl7_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f167,f108])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f33,f144,f140,f136])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    spl7_1 | ~spl7_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f34,f84,f80])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (27880)------------------------------
% 0.22/0.57  % (27880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (27880)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (27880)Memory used [KB]: 6396
% 0.22/0.57  % (27880)Time elapsed: 0.133 s
% 0.22/0.57  % (27880)------------------------------
% 0.22/0.57  % (27880)------------------------------
% 0.22/0.57  % (27875)Success in time 0.204 s
%------------------------------------------------------------------------------
