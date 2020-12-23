%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:39 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  157 (2428 expanded)
%              Number of leaves         :   20 ( 581 expanded)
%              Depth                    :   22
%              Number of atoms          :  462 (11439 expanded)
%              Number of equality atoms :   96 (3234 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f155,f168,f172,f312,f339,f492,f548,f635,f742])).

fof(f742,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f612,f718,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f718,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f717,f680])).

fof(f680,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f669,f676])).

fof(f676,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f609,f672])).

fof(f672,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f613,f650,f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f650,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f644,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f644,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f640,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f640,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f68,f612,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f613,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f569,f594])).

fof(f594,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f565,f306,f45])).

fof(f45,plain,(
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

fof(f306,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_6
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f565,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f564,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f564,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f104,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f50])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f569,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f568,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f568,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f37,f85])).

fof(f37,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f609,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f555,f594])).

fof(f555,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f554,f82])).

fof(f554,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f100,f85])).

fof(f100,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f38,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f669,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f650,f66])).

fof(f717,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f644,f671,f45])).

fof(f671,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f614,f650,f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f614,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f585,f594])).

fof(f585,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl5_1
    | spl5_4 ),
    inference(forward_demodulation,[],[f150,f82])).

fof(f150,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f612,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f567,f594])).

fof(f567,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f566,f69])).

fof(f566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f38,f85])).

fof(f635,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f310,f594])).

fof(f310,plain,
    ( k1_xboole_0 != sK3
    | spl5_7 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f548,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f72,f534])).

fof(f534,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f529,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f529,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK2))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f516,f82])).

fof(f516,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK2))
    | spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f157,f311])).

fof(f311,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f309])).

fof(f157,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f146,f49])).

fof(f146,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f492,plain,
    ( spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f439,f359,f440,f74])).

fof(f440,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f353,f422])).

fof(f422,plain,
    ( k1_xboole_0 = sK0
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f352,f359,f77])).

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
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f352,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f205,f311])).

fof(f205,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f150,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK2
    | spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f150,f125,f194,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f194,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl5_2 ),
    inference(forward_demodulation,[],[f188,f108])).

fof(f108,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl5_2 ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f86,f37,f38,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f188,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f125,f66])).

fof(f125,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_2 ),
    inference(forward_demodulation,[],[f122,f108])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(unit_resulting_resolution,[],[f103,f71,f107,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f107,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f39,f102])).

fof(f102,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f39,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f56,f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f353,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f208,f311])).

fof(f208,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f194,f198])).

fof(f359,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f236,f311])).

fof(f236,plain,
    ( ! [X0] : m1_subset_1(sK3,k1_zfmisc_1(X0))
    | spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f227,f49])).

fof(f227,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f224,f52])).

fof(f224,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f68,f211,f65])).

fof(f211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | spl5_4 ),
    inference(forward_demodulation,[],[f204,f69])).

fof(f204,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f125,f198])).

fof(f439,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f352,f422])).

fof(f339,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f72,f332,f49])).

fof(f332,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f68,f313,f65])).

fof(f313,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f307,f52])).

fof(f307,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f305])).

fof(f312,plain,
    ( ~ spl5_6
    | spl5_7
    | spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f215,f148,f84,f309,f305])).

fof(f215,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_2
    | spl5_4 ),
    inference(forward_demodulation,[],[f214,f69])).

fof(f214,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_2
    | spl5_4 ),
    inference(forward_demodulation,[],[f213,f198])).

fof(f213,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK2)
    | spl5_2
    | spl5_4 ),
    inference(forward_demodulation,[],[f209,f69])).

fof(f209,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK2)
    | spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f197,f198])).

fof(f197,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK2)
    | spl5_2 ),
    inference(resolution,[],[f191,f45])).

fof(f191,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f125,f50])).

fof(f172,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f36,f154])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f168,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f72,f159])).

fof(f159,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_2
    | spl5_3 ),
    inference(forward_demodulation,[],[f156,f108])).

fof(f156,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f103,f107,f146,f48])).

fof(f155,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f152,f148,f144])).

fof(f34,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f35,f84,f80])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (14415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (14434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (14418)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (14436)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (14421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (14436)Refutation not found, incomplete strategy% (14436)------------------------------
% 0.19/0.51  % (14436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (14419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (14423)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (14436)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14436)Memory used [KB]: 1791
% 0.19/0.52  % (14436)Time elapsed: 0.103 s
% 0.19/0.52  % (14436)------------------------------
% 0.19/0.52  % (14436)------------------------------
% 0.19/0.52  % (14438)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (14423)Refutation not found, incomplete strategy% (14423)------------------------------
% 0.19/0.52  % (14423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14423)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14423)Memory used [KB]: 10746
% 0.19/0.52  % (14423)Time elapsed: 0.117 s
% 0.19/0.52  % (14423)------------------------------
% 0.19/0.52  % (14423)------------------------------
% 0.19/0.52  % (14416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (14426)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (14430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (14420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (14440)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (14417)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (14444)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (14417)Refutation not found, incomplete strategy% (14417)------------------------------
% 0.19/0.54  % (14417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (14417)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (14417)Memory used [KB]: 10746
% 0.19/0.54  % (14417)Time elapsed: 0.124 s
% 0.19/0.54  % (14417)------------------------------
% 0.19/0.54  % (14417)------------------------------
% 0.19/0.54  % (14443)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (14441)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (14432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (14433)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  % (14422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (14435)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (14425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  % (14428)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (14429)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (14425)Refutation not found, incomplete strategy% (14425)------------------------------
% 1.36/0.55  % (14425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (14425)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (14425)Memory used [KB]: 10746
% 1.36/0.55  % (14425)Time elapsed: 0.149 s
% 1.36/0.55  % (14425)------------------------------
% 1.36/0.55  % (14425)------------------------------
% 1.36/0.55  % (14435)Refutation not found, incomplete strategy% (14435)------------------------------
% 1.36/0.55  % (14435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (14435)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (14435)Memory used [KB]: 10874
% 1.36/0.55  % (14435)Time elapsed: 0.154 s
% 1.36/0.55  % (14435)------------------------------
% 1.36/0.55  % (14435)------------------------------
% 1.36/0.55  % (14442)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (14439)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (14437)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.56  % (14424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.56  % (14431)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.57  % (14419)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f743,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f87,f155,f168,f172,f312,f339,f492,f548,f635,f742])).
% 1.57/0.57  fof(f742,plain,(
% 1.57/0.57    ~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f731])).
% 1.57/0.57  fof(f731,plain,(
% 1.57/0.57    $false | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f612,f718,f50])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.57/0.57  fof(f718,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6)),
% 1.57/0.57    inference(forward_demodulation,[],[f717,f680])).
% 1.57/0.57  fof(f680,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(forward_demodulation,[],[f669,f676])).
% 1.57/0.57  fof(f676,plain,(
% 1.57/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(backward_demodulation,[],[f609,f672])).
% 1.57/0.57  fof(f672,plain,(
% 1.57/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f613,f650,f73])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.57/0.57    inference(equality_resolution,[],[f60])).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(flattening,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.57/0.57  fof(f650,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f644,f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f5])).
% 1.57/0.57  fof(f644,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f640,f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.57  fof(f640,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f68,f612,f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    inference(cnf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.57/0.57  fof(f613,plain,(
% 1.57/0.57    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(backward_demodulation,[],[f569,f594])).
% 1.57/0.57  fof(f594,plain,(
% 1.57/0.57    k1_xboole_0 = sK3 | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f565,f306,f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.57  fof(f306,plain,(
% 1.57/0.57    r1_tarski(k1_xboole_0,sK3) | ~spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f305])).
% 1.57/0.57  fof(f305,plain,(
% 1.57/0.57    spl5_6 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.57  fof(f565,plain,(
% 1.57/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f564,f69])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.57/0.57  fof(f564,plain,(
% 1.57/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f104,f85])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    k1_xboole_0 = sK1 | ~spl5_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f84])).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    spl5_2 <=> k1_xboole_0 = sK1),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.57  fof(f104,plain,(
% 1.57/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f38,f50])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.57/0.57    inference(flattening,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.57/0.57    inference(ennf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.57/0.57    inference(negated_conjecture,[],[f19])).
% 1.57/0.57  fof(f19,conjecture,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.57/0.57  fof(f569,plain,(
% 1.57/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 1.57/0.57    inference(forward_demodulation,[],[f568,f82])).
% 1.57/0.57  fof(f82,plain,(
% 1.57/0.57    k1_xboole_0 = sK0 | ~spl5_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    spl5_1 <=> k1_xboole_0 = sK0),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.57  fof(f568,plain,(
% 1.57/0.57    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f37,f85])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f609,plain,(
% 1.57/0.57    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(backward_demodulation,[],[f555,f594])).
% 1.57/0.57  fof(f555,plain,(
% 1.57/0.57    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl5_1 | ~spl5_2)),
% 1.57/0.57    inference(forward_demodulation,[],[f554,f82])).
% 1.57/0.57  fof(f554,plain,(
% 1.57/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f100,f85])).
% 1.57/0.57  fof(f100,plain,(
% 1.57/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f38,f66])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.57/0.57  fof(f669,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f650,f66])).
% 1.57/0.57  fof(f717,plain,(
% 1.57/0.57    ~r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f644,f671,f45])).
% 1.57/0.57  fof(f671,plain,(
% 1.57/0.57    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f614,f650,f74])).
% 1.57/0.57  fof(f74,plain,(
% 1.57/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f59])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f614,plain,(
% 1.57/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_6)),
% 1.57/0.57    inference(backward_demodulation,[],[f585,f594])).
% 1.57/0.57  fof(f585,plain,(
% 1.57/0.57    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl5_1 | spl5_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f150,f82])).
% 1.57/0.57  fof(f150,plain,(
% 1.57/0.57    ~v1_funct_2(sK3,sK0,sK2) | spl5_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f148])).
% 1.57/0.57  fof(f148,plain,(
% 1.57/0.57    spl5_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.57  fof(f612,plain,(
% 1.57/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_2 | ~spl5_6)),
% 1.57/0.57    inference(backward_demodulation,[],[f567,f594])).
% 1.57/0.57  fof(f567,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f566,f69])).
% 1.57/0.57  fof(f566,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f38,f85])).
% 1.57/0.57  fof(f635,plain,(
% 1.57/0.57    ~spl5_2 | ~spl5_6 | spl5_7),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f631])).
% 1.57/0.57  fof(f631,plain,(
% 1.57/0.57    $false | (~spl5_2 | ~spl5_6 | spl5_7)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f310,f594])).
% 1.57/0.57  fof(f310,plain,(
% 1.57/0.57    k1_xboole_0 != sK3 | spl5_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f309])).
% 1.57/0.57  fof(f309,plain,(
% 1.57/0.57    spl5_7 <=> k1_xboole_0 = sK3),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.57/0.57  fof(f548,plain,(
% 1.57/0.57    ~spl5_1 | spl5_3 | ~spl5_7),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f540])).
% 1.57/0.57  fof(f540,plain,(
% 1.57/0.57    $false | (~spl5_1 | spl5_3 | ~spl5_7)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f72,f534])).
% 1.57/0.57  fof(f534,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl5_1 | spl5_3 | ~spl5_7)),
% 1.57/0.57    inference(forward_demodulation,[],[f529,f70])).
% 1.57/0.57  fof(f70,plain,(
% 1.57/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f41])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f4])).
% 1.57/0.57  fof(f529,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK2)) | (~spl5_1 | spl5_3 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f516,f82])).
% 1.57/0.57  fof(f516,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK2)) | (spl5_3 | ~spl5_7)),
% 1.57/0.57    inference(forward_demodulation,[],[f157,f311])).
% 1.57/0.57  fof(f311,plain,(
% 1.57/0.57    k1_xboole_0 = sK3 | ~spl5_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f309])).
% 1.57/0.57  fof(f157,plain,(
% 1.57/0.57    ~r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | spl5_3),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f146,f49])).
% 1.57/0.57  fof(f146,plain,(
% 1.57/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f144])).
% 1.57/0.57  fof(f144,plain,(
% 1.57/0.57    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f43])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f492,plain,(
% 1.57/0.57    spl5_2 | spl5_4 | ~spl5_7),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f487])).
% 1.57/0.57  fof(f487,plain,(
% 1.57/0.57    $false | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f439,f359,f440,f74])).
% 1.57/0.57  fof(f440,plain,(
% 1.57/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f353,f422])).
% 1.57/0.57  fof(f422,plain,(
% 1.57/0.57    k1_xboole_0 = sK0 | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f352,f359,f77])).
% 1.57/0.57  fof(f77,plain,(
% 1.57/0.57    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f76])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f57])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f352,plain,(
% 1.57/0.57    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f205,f311])).
% 1.57/0.57  fof(f205,plain,(
% 1.57/0.57    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(backward_demodulation,[],[f150,f198])).
% 1.57/0.57  fof(f198,plain,(
% 1.57/0.57    k1_xboole_0 = sK2 | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f150,f125,f194,f61])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f194,plain,(
% 1.57/0.57    sK0 = k1_relset_1(sK0,sK2,sK3) | spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f188,f108])).
% 1.57/0.57  fof(f108,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK3) | spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f100,f101])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | spl5_2),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f86,f37,f38,f62])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | spl5_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f84])).
% 1.57/0.57  fof(f188,plain,(
% 1.57/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl5_2),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f125,f66])).
% 1.57/0.57  fof(f125,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f122,f108])).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f103,f71,f107,f48])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(ennf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.57/0.57    inference(backward_demodulation,[],[f39,f102])).
% 1.57/0.57  fof(f102,plain,(
% 1.57/0.57    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f38,f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    v1_relat_1(sK3)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f56,f38,f55])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.57/0.57  fof(f353,plain,(
% 1.57/0.57    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f208,f311])).
% 1.57/0.57  fof(f208,plain,(
% 1.57/0.57    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(backward_demodulation,[],[f194,f198])).
% 1.57/0.57  fof(f359,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f236,f311])).
% 1.57/0.57  fof(f236,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f227,f49])).
% 1.57/0.57  fof(f227,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(sK3,X0)) ) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f224,f52])).
% 1.57/0.57  fof(f224,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f68,f211,f65])).
% 1.57/0.57  fof(f211,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f204,f69])).
% 1.57/0.57  fof(f204,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(backward_demodulation,[],[f125,f198])).
% 1.57/0.57  fof(f439,plain,(
% 1.57/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f352,f422])).
% 1.57/0.57  fof(f339,plain,(
% 1.57/0.57    spl5_6),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f337])).
% 1.57/0.57  fof(f337,plain,(
% 1.57/0.57    $false | spl5_6),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f72,f332,f49])).
% 1.57/0.57  fof(f332,plain,(
% 1.57/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl5_6),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f68,f313,f65])).
% 1.57/0.57  fof(f313,plain,(
% 1.57/0.57    r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | spl5_6),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f307,f52])).
% 1.57/0.57  fof(f307,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,sK3) | spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f305])).
% 1.57/0.57  fof(f312,plain,(
% 1.57/0.57    ~spl5_6 | spl5_7 | spl5_2 | spl5_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f215,f148,f84,f309,f305])).
% 1.57/0.57  fof(f215,plain,(
% 1.57/0.57    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f214,f69])).
% 1.57/0.57  fof(f214,plain,(
% 1.57/0.57    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK3) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f213,f198])).
% 1.57/0.57  fof(f213,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK2) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f209,f69])).
% 1.57/0.57  fof(f209,plain,(
% 1.57/0.57    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,sK2) | (spl5_2 | spl5_4)),
% 1.57/0.57    inference(backward_demodulation,[],[f197,f198])).
% 1.57/0.57  fof(f197,plain,(
% 1.57/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK2),sK3) | sK3 = k2_zfmisc_1(sK0,sK2) | spl5_2),
% 1.57/0.57    inference(resolution,[],[f191,f45])).
% 1.57/0.57  fof(f191,plain,(
% 1.57/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | spl5_2),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f125,f50])).
% 1.57/0.57  fof(f172,plain,(
% 1.57/0.57    spl5_5),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f169])).
% 1.57/0.57  fof(f169,plain,(
% 1.57/0.57    $false | spl5_5),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f36,f154])).
% 1.57/0.57  fof(f154,plain,(
% 1.57/0.57    ~v1_funct_1(sK3) | spl5_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f152])).
% 1.57/0.57  fof(f152,plain,(
% 1.57/0.57    spl5_5 <=> v1_funct_1(sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    v1_funct_1(sK3)),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f168,plain,(
% 1.57/0.57    spl5_2 | spl5_3),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f160])).
% 1.57/0.57  fof(f160,plain,(
% 1.57/0.57    $false | (spl5_2 | spl5_3)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f72,f159])).
% 1.57/0.57  fof(f159,plain,(
% 1.57/0.57    ~r1_tarski(sK0,sK0) | (spl5_2 | spl5_3)),
% 1.57/0.57    inference(forward_demodulation,[],[f156,f108])).
% 1.57/0.57  fof(f156,plain,(
% 1.57/0.57    ~r1_tarski(k1_relat_1(sK3),sK0) | spl5_3),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f103,f107,f146,f48])).
% 1.57/0.57  fof(f155,plain,(
% 1.57/0.57    ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f34,f152,f148,f144])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    spl5_1 | ~spl5_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f35,f84,f80])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (14419)------------------------------
% 1.57/0.57  % (14419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (14419)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (14419)Memory used [KB]: 6396
% 1.57/0.57  % (14419)Time elapsed: 0.140 s
% 1.57/0.57  % (14419)------------------------------
% 1.57/0.57  % (14419)------------------------------
% 1.57/0.57  % (14414)Success in time 0.21 s
%------------------------------------------------------------------------------
