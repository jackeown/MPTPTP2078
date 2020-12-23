%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
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
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f154,f176,f180,f423,f598,f627])).

fof(f627,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f477,f603,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f603,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f602,f536])).

fof(f536,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f482,f532])).

fof(f532,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f480,f508,f75])).

fof(f75,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f508,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f484,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f484,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f459,f458])).

fof(f458,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f455,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f455,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f69,f432,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f432,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f427,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f427,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f39,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f459,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f455,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
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

fof(f480,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f439,f458])).

fof(f439,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f426,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f426,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f38,f87])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f482,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f441,f458])).

fof(f441,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f430,f84])).

fof(f430,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f108,f87])).

fof(f108,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f39,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f602,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f601,f458])).

fof(f601,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl6_1
    | spl6_3 ),
    inference(forward_demodulation,[],[f164,f84])).

fof(f164,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f106,f110,f145,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f145,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f110,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f40,f105])).

fof(f105,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f22])).

% (551)Refutation not found, incomplete strategy% (551)------------------------------
% (551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f58,f39,f57])).

% (551)Termination reason: Refutation not found, incomplete strategy

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

% (551)Memory used [KB]: 10746
% (551)Time elapsed: 0.123 s
% (551)------------------------------
% (551)------------------------------
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

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f477,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f432,f458])).

fof(f598,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f477,f577,f52])).

fof(f577,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f576,f540])).

fof(f540,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f529,f536])).

fof(f529,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f508,f68])).

fof(f576,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f484,f531,f46])).

fof(f46,plain,(
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

fof(f531,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f479,f508,f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f479,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f438,f458])).

fof(f438,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl6_1
    | spl6_4 ),
    inference(backward_demodulation,[],[f149,f84])).

fof(f149,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f423,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f376,f315,f377,f76])).

fof(f377,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f278,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK0
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f276,f315,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f276,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f226,f250])).

fof(f250,plain,
    ( k1_xboole_0 = sK3
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f247,f47])).

fof(f247,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f232,f65])).

fof(f232,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f225,f71])).

fof(f225,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f128,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f149,f128,f195,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f195,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl6_2 ),
    inference(forward_demodulation,[],[f189,f111])).

fof(f111,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_2 ),
    inference(forward_demodulation,[],[f103,f104])).

fof(f104,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f88,f38,f39,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f103,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f39,f68])).

fof(f189,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f128,f68])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_2 ),
    inference(forward_demodulation,[],[f125,f111])).

fof(f125,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(unit_resulting_resolution,[],[f106,f73,f110,f50])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f226,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f149,f219])).

fof(f278,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f229,f250])).

fof(f229,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f195,f219])).

fof(f315,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f285,f51])).

fof(f285,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f251,f250])).

fof(f251,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | spl6_2
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f247,f54])).

fof(f376,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f276,f359])).

fof(f180,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f37,f153])).

fof(f153,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f74,f167])).

fof(f167,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f164,f111])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f154,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f35,f151,f147,f143])).

fof(f35,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f36,f86,f82])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (553)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.16/0.51  % (571)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.16/0.51  % (553)Refutation not found, incomplete strategy% (553)------------------------------
% 1.16/0.51  % (553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.51  % (560)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.16/0.51  % (553)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.51  
% 1.16/0.51  % (553)Memory used [KB]: 10746
% 1.16/0.51  % (553)Time elapsed: 0.106 s
% 1.16/0.51  % (553)------------------------------
% 1.16/0.51  % (553)------------------------------
% 1.16/0.52  % (546)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.16/0.52  % (552)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.16/0.52  % (568)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.52  % (544)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.16/0.52  % (567)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.16/0.52  % (543)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.16/0.52  % (557)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (545)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (555)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (551)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (545)Refutation not found, incomplete strategy% (545)------------------------------
% 1.29/0.53  % (545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (545)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (545)Memory used [KB]: 10746
% 1.29/0.53  % (545)Time elapsed: 0.115 s
% 1.29/0.53  % (545)------------------------------
% 1.29/0.53  % (545)------------------------------
% 1.29/0.53  % (547)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (548)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (549)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (563)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.54  % (574)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (573)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (558)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (570)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  % (576)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (569)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % (567)Refutation not found, incomplete strategy% (567)------------------------------
% 1.29/0.54  % (567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (567)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (567)Memory used [KB]: 1791
% 1.29/0.54  % (567)Time elapsed: 0.144 s
% 1.29/0.54  % (567)------------------------------
% 1.29/0.54  % (567)------------------------------
% 1.29/0.54  % (562)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (561)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (556)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.55  % (547)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f628,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(avatar_sat_refutation,[],[f89,f154,f176,f180,f423,f598,f627])).
% 1.29/0.55  fof(f627,plain,(
% 1.29/0.55    ~spl6_1 | ~spl6_2 | spl6_3),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f618])).
% 1.29/0.55  fof(f618,plain,(
% 1.29/0.55    $false | (~spl6_1 | ~spl6_2 | spl6_3)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f477,f603,f52])).
% 1.29/0.55  fof(f52,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f6])).
% 1.29/0.55  fof(f6,axiom,(
% 1.29/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.55  fof(f603,plain,(
% 1.29/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3)),
% 1.29/0.55    inference(forward_demodulation,[],[f602,f536])).
% 1.29/0.55  fof(f536,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(backward_demodulation,[],[f482,f532])).
% 1.29/0.55  fof(f532,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f480,f508,f75])).
% 1.29/0.55  fof(f75,plain,(
% 1.29/0.55    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.29/0.55    inference(equality_resolution,[],[f62])).
% 1.29/0.55  fof(f62,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.55    inference(flattening,[],[f31])).
% 1.29/0.55  fof(f31,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.55    inference(ennf_transformation,[],[f18])).
% 1.29/0.55  fof(f18,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.29/0.55  fof(f508,plain,(
% 1.29/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f484,f51])).
% 1.29/0.55  fof(f51,plain,(
% 1.29/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f6])).
% 1.29/0.55  fof(f484,plain,(
% 1.29/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_2),
% 1.29/0.55    inference(backward_demodulation,[],[f459,f458])).
% 1.29/0.55  fof(f458,plain,(
% 1.29/0.55    k1_xboole_0 = sK3 | ~spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f455,f47])).
% 1.29/0.55  fof(f47,plain,(
% 1.29/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.29/0.55    inference(ennf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.29/0.55  fof(f455,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f69,f432,f65])).
% 1.29/0.55  fof(f65,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f33])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.29/0.55  fof(f432,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 1.29/0.55    inference(forward_demodulation,[],[f427,f71])).
% 1.29/0.55  fof(f71,plain,(
% 1.29/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.29/0.55    inference(equality_resolution,[],[f43])).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.29/0.55  fof(f427,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.29/0.55    inference(backward_demodulation,[],[f39,f87])).
% 1.29/0.55  fof(f87,plain,(
% 1.29/0.55    k1_xboole_0 = sK1 | ~spl6_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f86])).
% 1.29/0.55  fof(f86,plain,(
% 1.29/0.55    spl6_2 <=> k1_xboole_0 = sK1),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.29/0.55    inference(flattening,[],[f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.29/0.55    inference(ennf_transformation,[],[f20])).
% 1.29/0.55  fof(f20,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.29/0.55    inference(negated_conjecture,[],[f19])).
% 1.29/0.55  fof(f19,conjecture,(
% 1.29/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.29/0.55  fof(f69,plain,(
% 1.29/0.55    v1_xboole_0(k1_xboole_0)),
% 1.29/0.55    inference(cnf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    v1_xboole_0(k1_xboole_0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.29/0.55  fof(f459,plain,(
% 1.29/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f455,f54])).
% 1.29/0.55  fof(f54,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f28])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.55  fof(f480,plain,(
% 1.29/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(backward_demodulation,[],[f439,f458])).
% 1.29/0.55  fof(f439,plain,(
% 1.29/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(backward_demodulation,[],[f426,f84])).
% 1.29/0.55  fof(f84,plain,(
% 1.29/0.55    k1_xboole_0 = sK0 | ~spl6_1),
% 1.29/0.55    inference(avatar_component_clause,[],[f82])).
% 1.29/0.55  fof(f82,plain,(
% 1.29/0.55    spl6_1 <=> k1_xboole_0 = sK0),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.29/0.55  fof(f426,plain,(
% 1.29/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_2),
% 1.29/0.55    inference(backward_demodulation,[],[f38,f87])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f482,plain,(
% 1.29/0.55    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(backward_demodulation,[],[f441,f458])).
% 1.29/0.55  fof(f441,plain,(
% 1.29/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(backward_demodulation,[],[f430,f84])).
% 1.29/0.55  fof(f430,plain,(
% 1.29/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl6_2),
% 1.29/0.55    inference(backward_demodulation,[],[f108,f87])).
% 1.29/0.55  fof(f108,plain,(
% 1.29/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.29/0.55    inference(resolution,[],[f39,f68])).
% 1.29/0.55  fof(f68,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f34])).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.55    inference(ennf_transformation,[],[f14])).
% 1.29/0.55  fof(f14,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.29/0.55  fof(f602,plain,(
% 1.29/0.55    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3)),
% 1.29/0.55    inference(forward_demodulation,[],[f601,f458])).
% 1.29/0.55  fof(f601,plain,(
% 1.29/0.55    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (~spl6_1 | spl6_3)),
% 1.29/0.55    inference(forward_demodulation,[],[f164,f84])).
% 1.29/0.55  fof(f164,plain,(
% 1.29/0.55    ~r1_tarski(k1_relat_1(sK3),sK0) | spl6_3),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f106,f110,f145,f50])).
% 1.29/0.55  fof(f50,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f27])).
% 1.29/0.55  fof(f27,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.29/0.55    inference(flattening,[],[f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.29/0.55    inference(ennf_transformation,[],[f16])).
% 1.29/0.55  fof(f16,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.29/0.55  fof(f145,plain,(
% 1.29/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_3),
% 1.29/0.55    inference(avatar_component_clause,[],[f143])).
% 1.29/0.55  fof(f143,plain,(
% 1.29/0.55    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.29/0.55  fof(f110,plain,(
% 1.29/0.55    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.29/0.55    inference(backward_demodulation,[],[f40,f105])).
% 1.29/0.55  fof(f105,plain,(
% 1.29/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f39,f56])).
% 1.29/0.55  fof(f56,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.55    inference(ennf_transformation,[],[f15])).
% 1.29/0.55  fof(f15,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.29/0.55  fof(f40,plain,(
% 1.29/0.55    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  % (551)Refutation not found, incomplete strategy% (551)------------------------------
% 1.29/0.55  % (551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  fof(f106,plain,(
% 1.29/0.55    v1_relat_1(sK3)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f58,f39,f57])).
% 1.29/0.55  % (551)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  fof(f57,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f30])).
% 1.29/0.55  % (551)Memory used [KB]: 10746
% 1.29/0.55  % (551)Time elapsed: 0.123 s
% 1.29/0.55  % (551)------------------------------
% 1.29/0.55  % (551)------------------------------
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f8])).
% 1.29/0.55  fof(f8,axiom,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.29/0.55  fof(f58,plain,(
% 1.29/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f10])).
% 1.29/0.55  fof(f10,axiom,(
% 1.29/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.29/0.55  fof(f477,plain,(
% 1.29/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 1.29/0.55    inference(backward_demodulation,[],[f432,f458])).
% 1.29/0.55  fof(f598,plain,(
% 1.29/0.55    ~spl6_1 | ~spl6_2 | spl6_4),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f589])).
% 1.29/0.55  fof(f589,plain,(
% 1.29/0.55    $false | (~spl6_1 | ~spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f477,f577,f52])).
% 1.29/0.55  fof(f577,plain,(
% 1.29/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 1.29/0.55    inference(forward_demodulation,[],[f576,f540])).
% 1.29/0.55  fof(f540,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_1 | ~spl6_2)),
% 1.29/0.55    inference(forward_demodulation,[],[f529,f536])).
% 1.29/0.55  fof(f529,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f508,f68])).
% 1.29/0.55  fof(f576,plain,(
% 1.29/0.55    ~r1_tarski(k1_relset_1(k1_xboole_0,sK2,k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f484,f531,f46])).
% 1.29/0.55  fof(f46,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.55  fof(f531,plain,(
% 1.29/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f479,f508,f76])).
% 1.29/0.55  fof(f76,plain,(
% 1.29/0.55    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.29/0.55    inference(equality_resolution,[],[f61])).
% 1.29/0.55  fof(f61,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f32])).
% 1.29/0.55  fof(f479,plain,(
% 1.29/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_1 | ~spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f438,f458])).
% 1.29/0.55  fof(f438,plain,(
% 1.29/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl6_1 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f149,f84])).
% 1.29/0.55  fof(f149,plain,(
% 1.29/0.55    ~v1_funct_2(sK3,sK0,sK2) | spl6_4),
% 1.29/0.55    inference(avatar_component_clause,[],[f147])).
% 1.29/0.55  fof(f147,plain,(
% 1.29/0.55    spl6_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.29/0.55  fof(f423,plain,(
% 1.29/0.55    spl6_2 | spl6_4),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f418])).
% 1.29/0.55  fof(f418,plain,(
% 1.29/0.55    $false | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f376,f315,f377,f76])).
% 1.29/0.55  fof(f377,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f278,f359])).
% 1.29/0.55  fof(f359,plain,(
% 1.29/0.55    k1_xboole_0 = sK0 | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f276,f315,f79])).
% 1.29/0.55  fof(f79,plain,(
% 1.29/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.29/0.55    inference(equality_resolution,[],[f78])).
% 1.29/0.55  fof(f78,plain,(
% 1.29/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.29/0.55    inference(equality_resolution,[],[f59])).
% 1.29/0.55  fof(f59,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f32])).
% 1.29/0.55  fof(f276,plain,(
% 1.29/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f226,f250])).
% 1.29/0.55  fof(f250,plain,(
% 1.29/0.55    k1_xboole_0 = sK3 | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f247,f47])).
% 1.29/0.55  fof(f247,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f69,f232,f65])).
% 1.29/0.55  fof(f232,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(forward_demodulation,[],[f225,f71])).
% 1.29/0.55  fof(f225,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f128,f219])).
% 1.29/0.55  fof(f219,plain,(
% 1.29/0.55    k1_xboole_0 = sK2 | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f149,f128,f195,f63])).
% 1.29/0.55  fof(f63,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f32])).
% 1.29/0.55  fof(f195,plain,(
% 1.29/0.55    sK0 = k1_relset_1(sK0,sK2,sK3) | spl6_2),
% 1.29/0.55    inference(forward_demodulation,[],[f189,f111])).
% 1.29/0.55  fof(f111,plain,(
% 1.29/0.55    sK0 = k1_relat_1(sK3) | spl6_2),
% 1.29/0.55    inference(forward_demodulation,[],[f103,f104])).
% 1.29/0.55  fof(f104,plain,(
% 1.29/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f88,f38,f39,f64])).
% 1.29/0.55  fof(f64,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f32])).
% 1.29/0.55  fof(f88,plain,(
% 1.29/0.55    k1_xboole_0 != sK1 | spl6_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f86])).
% 1.29/0.55  fof(f103,plain,(
% 1.29/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f39,f68])).
% 1.29/0.55  fof(f189,plain,(
% 1.29/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | spl6_2),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f128,f68])).
% 1.29/0.55  fof(f128,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_2),
% 1.29/0.55    inference(forward_demodulation,[],[f125,f111])).
% 1.29/0.55  fof(f125,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f106,f73,f110,f50])).
% 1.29/0.55  fof(f73,plain,(
% 1.29/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.29/0.55    inference(equality_resolution,[],[f45])).
% 1.29/0.55  fof(f45,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f226,plain,(
% 1.29/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f149,f219])).
% 1.29/0.55  fof(f278,plain,(
% 1.29/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f229,f250])).
% 1.29/0.55  fof(f229,plain,(
% 1.29/0.55    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f195,f219])).
% 1.29/0.55  fof(f315,plain,(
% 1.29/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f285,f51])).
% 1.29/0.55  fof(f285,plain,(
% 1.29/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f251,f250])).
% 1.29/0.55  fof(f251,plain,(
% 1.29/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f247,f54])).
% 1.29/0.55  fof(f376,plain,(
% 1.29/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | spl6_4)),
% 1.29/0.55    inference(backward_demodulation,[],[f276,f359])).
% 1.29/0.55  fof(f180,plain,(
% 1.29/0.55    spl6_5),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f177])).
% 1.29/0.55  fof(f177,plain,(
% 1.29/0.55    $false | spl6_5),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f37,f153])).
% 1.29/0.55  fof(f153,plain,(
% 1.29/0.55    ~v1_funct_1(sK3) | spl6_5),
% 1.29/0.55    inference(avatar_component_clause,[],[f151])).
% 1.29/0.55  fof(f151,plain,(
% 1.29/0.55    spl6_5 <=> v1_funct_1(sK3)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.29/0.55  fof(f37,plain,(
% 1.29/0.55    v1_funct_1(sK3)),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f176,plain,(
% 1.29/0.55    spl6_2 | spl6_3),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f168])).
% 1.29/0.55  fof(f168,plain,(
% 1.29/0.55    $false | (spl6_2 | spl6_3)),
% 1.29/0.55    inference(unit_resulting_resolution,[],[f74,f167])).
% 1.29/0.55  fof(f167,plain,(
% 1.29/0.55    ~r1_tarski(sK0,sK0) | (spl6_2 | spl6_3)),
% 1.29/0.55    inference(forward_demodulation,[],[f164,f111])).
% 1.29/0.55  fof(f74,plain,(
% 1.29/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.29/0.55    inference(equality_resolution,[],[f44])).
% 1.29/0.55  fof(f44,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f154,plain,(
% 1.29/0.55    ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.29/0.55    inference(avatar_split_clause,[],[f35,f151,f147,f143])).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f89,plain,(
% 1.29/0.55    spl6_1 | ~spl6_2),
% 1.29/0.55    inference(avatar_split_clause,[],[f36,f86,f82])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (547)------------------------------
% 1.29/0.55  % (547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (547)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (547)Memory used [KB]: 6396
% 1.29/0.55  % (547)Time elapsed: 0.137 s
% 1.29/0.55  % (547)------------------------------
% 1.29/0.55  % (547)------------------------------
% 1.29/0.55  % (554)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (542)Success in time 0.193 s
%------------------------------------------------------------------------------
