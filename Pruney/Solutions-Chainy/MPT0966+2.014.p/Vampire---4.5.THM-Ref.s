%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 (5802 expanded)
%              Number of leaves         :   22 (1361 expanded)
%              Depth                    :   26
%              Number of atoms          :  464 (26916 expanded)
%              Number of equality atoms :   90 (7196 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f733,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f177,f188,f192,f436,f712,f732])).

fof(f732,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f723])).

fof(f723,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f515,f717,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f717,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f716,f586])).

fof(f586,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f516,f510,f53])).

fof(f53,plain,(
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

fof(f510,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f445,f490])).

fof(f490,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f476,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f476,plain,
    ( ! [X0] : r1_xboole_0(X0,sK3)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f472,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f472,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f81,f443,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f443,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f439,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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

fof(f439,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f46,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

% (13949)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f445,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f155,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f155,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f128,f123,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f123,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f128,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f62,f46,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f516,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f473,f490])).

fof(f473,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f472,f58])).

fof(f716,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f715,f490])).

fof(f715,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl6_1
    | spl6_3 ),
    inference(forward_demodulation,[],[f179,f98])).

fof(f179,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f128,f130,f168,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f168,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f130,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f47,f127])).

fof(f127,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f47,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f515,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f472,f490])).

fof(f712,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f703])).

fof(f703,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f515,f694,f58])).

fof(f694,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f693,f682])).

fof(f682,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f671,f586])).

fof(f671,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f649,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f649,plain,
    ( ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f516,f516,f604])).

fof(f604,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_xboole_0,X5)
        | ~ r1_tarski(k1_xboole_0,X4)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f594,f601])).

fof(f601,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f494,f586,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f494,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f128,f490])).

fof(f594,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_xboole_0,X4)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X5) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f523,f586])).

fof(f523,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X5)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X4) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f522,f490])).

fof(f522,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X5)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X4)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f503,f490])).

fof(f503,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X4)
        | ~ r1_tarski(k2_relat_1(sK3),X5)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f146,f490])).

fof(f146,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_relat_1(sK3),X4)
      | ~ r1_tarski(k2_relat_1(sK3),X5)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f128,f56])).

fof(f693,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f516,f673,f53])).

fof(f673,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f511,f649,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f511,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f448,f490])).

fof(f448,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl6_1
    | spl6_4 ),
    inference(backward_demodulation,[],[f172,f98])).

fof(f172,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f436,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f277,f431])).

fof(f431,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f427,f84])).

fof(f427,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f385,f386,f89])).

fof(f386,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f275,f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK0
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f264,f376])).

fof(f376,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f263,f361,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f361,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f279,f271,f53])).

fof(f271,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f211,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK3
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f231,f82])).

fof(f231,plain,
    ( ! [X0] : r1_xboole_0(X0,sK3)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f225,f76])).

fof(f225,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f81,f219,f73])).

fof(f219,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f213,f84])).

fof(f213,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f162,f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK2
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f172,f162,f206,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f206,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl6_2 ),
    inference(forward_demodulation,[],[f202,f131])).

fof(f131,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_2 ),
    inference(forward_demodulation,[],[f125,f126])).

fof(f126,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f102,f45,f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f125,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f46,f70])).

fof(f202,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f70])).

fof(f162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_2 ),
    inference(forward_demodulation,[],[f160,f131])).

fof(f160,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(unit_resulting_resolution,[],[f128,f86,f130,f56])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f211,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f130,f208])).

fof(f279,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f226,f253])).

fof(f226,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f225,f58])).

fof(f263,plain,
    ( v1_relat_1(k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f128,f253])).

fof(f264,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f131,f253])).

fof(f275,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f217,f253])).

fof(f217,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f206,f208])).

fof(f385,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f272,f379])).

fof(f272,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f214,f253])).

fof(f214,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f172,f208])).

fof(f277,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f219,f253])).

fof(f192,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f44,f176])).

fof(f176,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f188,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f87,f180])).

fof(f180,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f179,f131])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f177,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f42,f174,f170,f166])).

fof(f42,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f43,f100,f96])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (13922)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (13933)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (13926)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13932)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13944)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13936)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13924)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13937)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13924)Refutation not found, incomplete strategy% (13924)------------------------------
% 0.21/0.53  % (13924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13924)Memory used [KB]: 10746
% 0.21/0.53  % (13924)Time elapsed: 0.117 s
% 0.21/0.53  % (13924)------------------------------
% 0.21/0.53  % (13924)------------------------------
% 0.21/0.53  % (13927)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (13923)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13925)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (13934)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13932)Refutation not found, incomplete strategy% (13932)------------------------------
% 0.21/0.53  % (13932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13939)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (13931)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (13950)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (13930)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (13940)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13932)Memory used [KB]: 10746
% 0.21/0.54  % (13932)Time elapsed: 0.092 s
% 0.21/0.54  % (13932)------------------------------
% 0.21/0.54  % (13932)------------------------------
% 0.21/0.54  % (13944)Refutation not found, incomplete strategy% (13944)------------------------------
% 0.21/0.54  % (13944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13951)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (13943)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (13930)Refutation not found, incomplete strategy% (13930)------------------------------
% 0.21/0.54  % (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13930)Memory used [KB]: 10874
% 0.21/0.54  % (13930)Time elapsed: 0.135 s
% 0.21/0.54  % (13930)------------------------------
% 0.21/0.54  % (13930)------------------------------
% 0.21/0.54  % (13929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (13928)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13926)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f733,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f103,f177,f188,f192,f436,f712,f732])).
% 0.21/0.54  fof(f732,plain,(
% 0.21/0.54    ~spl6_1 | ~spl6_2 | spl6_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f723])).
% 0.21/0.54  fof(f723,plain,(
% 0.21/0.54    $false | (~spl6_1 | ~spl6_2 | spl6_3)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f515,f717,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f717,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3)),
% 0.21/0.54    inference(forward_demodulation,[],[f716,f586])).
% 0.21/0.54  fof(f586,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f516,f510,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f510,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.21/0.54    inference(backward_demodulation,[],[f445,f490])).
% 0.21/0.54  fof(f490,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f476,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.54  fof(f476,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,sK3)) ) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f472,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f472,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f81,f443,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.54  fof(f443,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 0.21/0.54    inference(forward_demodulation,[],[f439,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 0.21/0.54    inference(backward_demodulation,[],[f46,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % (13949)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f20])).
% 0.21/0.54  fof(f20,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~spl6_1),
% 0.21/0.54    inference(backward_demodulation,[],[f155,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f128,f123,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    v4_relat_1(sK3,sK0)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f46,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    v1_relat_1(sK3)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f62,f46,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f516,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.21/0.55    inference(backward_demodulation,[],[f473,f490])).
% 0.21/0.55  fof(f473,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_2),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f472,f58])).
% 0.21/0.55  fof(f716,plain,(
% 0.21/0.55    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3)),
% 0.21/0.55    inference(forward_demodulation,[],[f715,f490])).
% 0.21/0.55  fof(f715,plain,(
% 0.21/0.55    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (~spl6_1 | spl6_3)),
% 0.21/0.55    inference(forward_demodulation,[],[f179,f98])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ~r1_tarski(k1_relat_1(sK3),sK0) | spl6_3),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f130,f168,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f166])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f47,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f46,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f515,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.55    inference(backward_demodulation,[],[f472,f490])).
% 0.21/0.55  fof(f712,plain,(
% 0.21/0.55    ~spl6_1 | ~spl6_2 | spl6_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f703])).
% 0.21/0.55  fof(f703,plain,(
% 0.21/0.55    $false | (~spl6_1 | ~spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f515,f694,f58])).
% 0.21/0.55  fof(f694,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f693,f682])).
% 0.21/0.55  fof(f682,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(forward_demodulation,[],[f671,f586])).
% 0.21/0.55  fof(f671,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f649,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.55  fof(f649,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f516,f516,f604])).
% 0.21/0.55  fof(f604,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r1_tarski(k1_xboole_0,X5) | ~r1_tarski(k1_xboole_0,X4) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(backward_demodulation,[],[f594,f601])).
% 0.21/0.55  fof(f601,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f494,f586,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.55  fof(f494,plain,(
% 0.21/0.55    v1_relat_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.55    inference(backward_demodulation,[],[f128,f490])).
% 0.21/0.55  fof(f594,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r1_tarski(k1_xboole_0,X4) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X5)) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.55    inference(backward_demodulation,[],[f523,f586])).
% 0.21/0.55  fof(f523,plain,(
% 0.21/0.55    ( ! [X4,X5] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X5) | ~r1_tarski(k1_relat_1(k1_xboole_0),X4)) ) | ~spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f522,f490])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r1_tarski(k2_relat_1(k1_xboole_0),X5) | ~r1_tarski(k1_relat_1(k1_xboole_0),X4) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f503,f490])).
% 0.21/0.55  fof(f503,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(k1_xboole_0),X4) | ~r1_tarski(k2_relat_1(sK3),X5) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl6_2),
% 0.21/0.55    inference(backward_demodulation,[],[f146,f490])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(sK3),X4) | ~r1_tarski(k2_relat_1(sK3),X5) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.21/0.55    inference(resolution,[],[f128,f56])).
% 0.21/0.55  fof(f693,plain,(
% 0.21/0.55    ~r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f516,f673,f53])).
% 0.21/0.55  fof(f673,plain,(
% 0.21/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f511,f649,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f448,f490])).
% 0.21/0.55  fof(f448,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl6_1 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f172,f98])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,sK0,sK2) | spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    spl6_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f436,plain,(
% 0.21/0.55    spl6_2 | spl6_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f433])).
% 0.21/0.55  fof(f433,plain,(
% 0.21/0.55    $false | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f277,f431])).
% 0.21/0.55  fof(f431,plain,(
% 0.21/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f427,f84])).
% 0.21/0.55  fof(f427,plain,(
% 0.21/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f385,f386,f89])).
% 0.21/0.55  fof(f386,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f275,f379])).
% 0.21/0.55  fof(f379,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f264,f376])).
% 0.21/0.55  fof(f376,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f263,f361,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f361,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f279,f271,f53])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f211,f253])).
% 0.21/0.55  fof(f253,plain,(
% 0.21/0.55    k1_xboole_0 = sK3 | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f231,f82])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ( ! [X0] : (r1_xboole_0(X0,sK3)) ) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f225,f76])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f81,f219,f73])).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f213,f84])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f162,f208])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f172,f162,f206,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,sK2,sK3) | spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f202,f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK3) | spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f125,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_2),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f102,f45,f46,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f100])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f46,f70])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl6_2),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f162,f70])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_2),
% 0.21/0.55    inference(forward_demodulation,[],[f160,f131])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f86,f130,f56])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK3),k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f130,f208])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f226,f253])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f225,f58])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    v1_relat_1(k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f128,f253])).
% 0.21/0.55  fof(f264,plain,(
% 0.21/0.55    sK0 = k1_relat_1(k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f131,f253])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f217,f253])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f206,f208])).
% 0.21/0.55  fof(f385,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f272,f379])).
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f214,f253])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f172,f208])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl6_2 | spl6_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f219,f253])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl6_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    $false | spl6_5),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f44,f176])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    ~v1_funct_1(sK3) | spl6_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    spl6_5 <=> v1_funct_1(sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    v1_funct_1(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    spl6_2 | spl6_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    $false | (spl6_2 | spl6_3)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f87,f180])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ~r1_tarski(sK0,sK0) | (spl6_2 | spl6_3)),
% 0.21/0.55    inference(forward_demodulation,[],[f179,f131])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f174,f170,f166])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    spl6_1 | ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f43,f100,f96])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (13926)------------------------------
% 0.21/0.55  % (13926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13926)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (13926)Memory used [KB]: 6396
% 0.21/0.55  % (13926)Time elapsed: 0.141 s
% 0.21/0.55  % (13926)------------------------------
% 0.21/0.55  % (13926)------------------------------
% 0.21/0.55  % (13935)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (13948)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (13938)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (13939)Refutation not found, incomplete strategy% (13939)------------------------------
% 0.21/0.55  % (13939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13939)Memory used [KB]: 10746
% 0.21/0.55  % (13939)Time elapsed: 0.129 s
% 0.21/0.55  % (13939)------------------------------
% 0.21/0.55  % (13939)------------------------------
% 0.21/0.55  % (13942)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13947)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13945)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (13941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (13946)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (13942)Refutation not found, incomplete strategy% (13942)------------------------------
% 0.21/0.56  % (13942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13942)Memory used [KB]: 10874
% 0.21/0.56  % (13942)Time elapsed: 0.152 s
% 0.21/0.56  % (13942)------------------------------
% 0.21/0.56  % (13942)------------------------------
% 0.21/0.56  % (13913)Success in time 0.199 s
%------------------------------------------------------------------------------
