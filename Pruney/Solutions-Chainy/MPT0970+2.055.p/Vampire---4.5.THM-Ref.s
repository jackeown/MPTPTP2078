%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:56 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 374 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  249 (1334 expanded)
%              Number of equality atoms :   59 ( 322 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f172,f176,f243,f468,f702,f712])).

fof(f712,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f98,f102,f104,f701])).

fof(f701,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK7(sK1,X2)),sK0)
        | r1_tarski(sK1,X2)
        | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl8_13
  <=> ! [X2] :
        ( ~ r2_hidden(sK3(sK7(sK1,X2)),sK0)
        | r1_tarski(sK1,X2)
        | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f104,plain,(
    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f101,f26])).

fof(f26,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f101,plain,(
    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f98,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f102,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f98,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f84,f96,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f96,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f86,f44])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(X0,sK1),k2_relat_1(sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f80,f45])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f78,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f84,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f31,f72])).

fof(f31,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f702,plain,
    ( ~ spl8_2
    | ~ spl8_7
    | spl8_13
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f472,f169,f700,f233,f113])).

fof(f113,plain,
    ( spl8_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f233,plain,
    ( spl8_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f169,plain,
    ( spl8_5
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f472,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK7(sK1,X2)),sK0)
        | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK1,X2) )
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f200,f171])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f200,plain,(
    ! [X2] :
      ( r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(sK7(sK1,X2)),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f60,f82])).

fof(f82,plain,(
    ! [X2] :
      ( sK7(sK1,X2) = k1_funct_1(sK2,sK3(sK7(sK1,X2)))
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f27,f44])).

fof(f27,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f468,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f54,f417])).

fof(f417,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f137,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f137,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f101,f130,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f130,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f54,f102,f43])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f243,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f28,f235])).

fof(f235,plain,
    ( ~ v1_funct_1(sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f233])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f176,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f30,f163])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f172,plain,
    ( ~ spl8_3
    | spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f79,f169,f165,f161])).

fof(f79,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f70,f71])).

fof(f71,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f30,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f29,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f47,f30,f115,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:33:39 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.45  % (29988)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.45  % (30008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.46  % (29999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.46  % (29987)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.46  % (29986)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.47  % (29995)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.47  % (30010)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.47  % (29991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.48  % (30002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.48  % (30013)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.49  % (29994)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.49  % (29994)Refutation not found, incomplete strategy% (29994)------------------------------
% 0.18/0.49  % (29994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (29997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.49  % (30004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.49  % (29998)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.49  % (30012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.50  % (29996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.50  % (29994)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (29994)Memory used [KB]: 10746
% 0.18/0.50  % (29994)Time elapsed: 0.110 s
% 0.18/0.50  % (29994)------------------------------
% 0.18/0.50  % (29994)------------------------------
% 0.18/0.50  % (29984)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.50  % (29985)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.50  % (29988)Refutation found. Thanks to Tanya!
% 0.18/0.50  % SZS status Theorem for theBenchmark
% 0.18/0.50  % SZS output start Proof for theBenchmark
% 0.18/0.50  fof(f713,plain,(
% 0.18/0.50    $false),
% 0.18/0.50    inference(avatar_sat_refutation,[],[f126,f172,f176,f243,f468,f702,f712])).
% 0.18/0.50  fof(f712,plain,(
% 0.18/0.50    ~spl8_13),
% 0.18/0.50    inference(avatar_contradiction_clause,[],[f707])).
% 0.18/0.50  fof(f707,plain,(
% 0.18/0.50    $false | ~spl8_13),
% 0.18/0.50    inference(unit_resulting_resolution,[],[f98,f102,f104,f701])).
% 0.18/0.50  fof(f701,plain,(
% 0.18/0.50    ( ! [X2] : (~r2_hidden(sK3(sK7(sK1,X2)),sK0) | r1_tarski(sK1,X2) | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))) ) | ~spl8_13),
% 0.18/0.50    inference(avatar_component_clause,[],[f700])).
% 0.18/0.51  fof(f700,plain,(
% 0.18/0.51    spl8_13 <=> ! [X2] : (~r2_hidden(sK3(sK7(sK1,X2)),sK0) | r1_tarski(sK1,X2) | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.18/0.51  fof(f104,plain,(
% 0.18/0.51    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f101,f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f15,plain,(
% 0.18/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.51    inference(flattening,[],[f14])).
% 0.18/0.51  fof(f14,plain,(
% 0.18/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.18/0.51    inference(ennf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.18/0.51    inference(negated_conjecture,[],[f12])).
% 0.18/0.51  fof(f12,conjecture,(
% 0.18/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.18/0.51  fof(f101,plain,(
% 0.18/0.51    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f98,f44])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.51  fof(f102,plain,(
% 0.18/0.51    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f98,f45])).
% 0.18/0.51  fof(f45,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f20])).
% 0.18/0.51  fof(f98,plain,(
% 0.18/0.51    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f84,f96,f36])).
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.18/0.51    inference(cnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.51  fof(f96,plain,(
% 0.18/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f94])).
% 0.18/0.51  fof(f94,plain,(
% 0.18/0.51    r1_tarski(k2_relat_1(sK2),sK1) | r1_tarski(k2_relat_1(sK2),sK1)),
% 0.18/0.51    inference(resolution,[],[f86,f44])).
% 0.18/0.51  fof(f86,plain,(
% 0.18/0.51    ( ! [X0] : (~r2_hidden(sK7(X0,sK1),k2_relat_1(sK2)) | r1_tarski(X0,sK1)) )),
% 0.18/0.51    inference(resolution,[],[f80,f45])).
% 0.18/0.51  fof(f80,plain,(
% 0.18/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.18/0.51    inference(resolution,[],[f78,f46])).
% 0.18/0.51  fof(f46,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f21])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f4])).
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.18/0.51  fof(f78,plain,(
% 0.18/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.18/0.51    inference(backward_demodulation,[],[f73,f72])).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f30,f33])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f30,f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.18/0.51  fof(f84,plain,(
% 0.18/0.51    sK1 != k2_relat_1(sK2)),
% 0.18/0.51    inference(superposition,[],[f31,f72])).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f702,plain,(
% 0.18/0.51    ~spl8_2 | ~spl8_7 | spl8_13 | ~spl8_5),
% 0.18/0.51    inference(avatar_split_clause,[],[f472,f169,f700,f233,f113])).
% 0.18/0.51  fof(f113,plain,(
% 0.18/0.51    spl8_2 <=> v1_relat_1(sK2)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.18/0.51  fof(f233,plain,(
% 0.18/0.51    spl8_7 <=> v1_funct_1(sK2)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.18/0.51  fof(f169,plain,(
% 0.18/0.51    spl8_5 <=> sK0 = k1_relat_1(sK2)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.18/0.51  fof(f472,plain,(
% 0.18/0.51    ( ! [X2] : (~r2_hidden(sK3(sK7(sK1,X2)),sK0) | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(sK1,X2)) ) | ~spl8_5),
% 0.18/0.51    inference(backward_demodulation,[],[f200,f171])).
% 0.18/0.51  fof(f171,plain,(
% 0.18/0.51    sK0 = k1_relat_1(sK2) | ~spl8_5),
% 0.18/0.51    inference(avatar_component_clause,[],[f169])).
% 0.18/0.51  fof(f200,plain,(
% 0.18/0.51    ( ! [X2] : (r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(sK7(sK1,X2)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK1,X2)) )),
% 0.18/0.51    inference(superposition,[],[f60,f82])).
% 0.18/0.51  fof(f82,plain,(
% 0.18/0.51    ( ! [X2] : (sK7(sK1,X2) = k1_funct_1(sK2,sK3(sK7(sK1,X2))) | r1_tarski(sK1,X2)) )),
% 0.18/0.51    inference(resolution,[],[f27,f44])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f60,plain,(
% 0.18/0.51    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.51    inference(equality_resolution,[],[f59])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.18/0.51    inference(equality_resolution,[],[f42])).
% 0.18/0.51  fof(f42,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(flattening,[],[f18])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.18/0.51  fof(f468,plain,(
% 0.18/0.51    ~spl8_4),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f459])).
% 0.18/0.51  fof(f459,plain,(
% 0.18/0.51    $false | ~spl8_4),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f54,f417])).
% 0.18/0.51  fof(f417,plain,(
% 0.18/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl8_4),
% 0.18/0.51    inference(backward_demodulation,[],[f137,f167])).
% 0.18/0.51  fof(f167,plain,(
% 0.18/0.51    k1_xboole_0 = sK1 | ~spl8_4),
% 0.18/0.51    inference(avatar_component_clause,[],[f165])).
% 0.18/0.51  fof(f165,plain,(
% 0.18/0.51    spl8_4 <=> k1_xboole_0 = sK1),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.18/0.51  fof(f137,plain,(
% 0.18/0.51    ~r1_tarski(sK1,k1_xboole_0)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f101,f130,f43])).
% 0.18/0.51  fof(f43,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f20])).
% 0.18/0.51  fof(f130,plain,(
% 0.18/0.51    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k1_xboole_0)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f54,f102,f43])).
% 0.18/0.51  fof(f54,plain,(
% 0.18/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.51  fof(f243,plain,(
% 0.18/0.51    spl8_7),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f240])).
% 0.18/0.51  fof(f240,plain,(
% 0.18/0.51    $false | spl8_7),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f28,f235])).
% 0.18/0.51  fof(f235,plain,(
% 0.18/0.51    ~v1_funct_1(sK2) | spl8_7),
% 0.18/0.51    inference(avatar_component_clause,[],[f233])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    v1_funct_1(sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f176,plain,(
% 0.18/0.51    spl8_3),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f173])).
% 0.18/0.51  fof(f173,plain,(
% 0.18/0.51    $false | spl8_3),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f30,f163])).
% 0.18/0.51  fof(f163,plain,(
% 0.18/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_3),
% 0.18/0.51    inference(avatar_component_clause,[],[f161])).
% 0.18/0.51  fof(f161,plain,(
% 0.18/0.51    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.18/0.51  fof(f172,plain,(
% 0.18/0.51    ~spl8_3 | spl8_4 | spl8_5),
% 0.18/0.51    inference(avatar_split_clause,[],[f79,f169,f165,f161])).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.51    inference(backward_demodulation,[],[f70,f71])).
% 0.18/0.51  fof(f71,plain,(
% 0.18/0.51    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f30,f55])).
% 0.18/0.51  fof(f55,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f24])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.51    inference(resolution,[],[f29,f53])).
% 0.18/0.51  fof(f53,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(flattening,[],[f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.51    inference(cnf_transformation,[],[f15])).
% 0.18/0.51  fof(f126,plain,(
% 0.18/0.51    spl8_2),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f121])).
% 0.18/0.51  fof(f121,plain,(
% 0.18/0.51    $false | spl8_2),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f47,f30,f115,f56])).
% 0.18/0.51  fof(f56,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f25])).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.51  fof(f115,plain,(
% 0.18/0.51    ~v1_relat_1(sK2) | spl8_2),
% 0.18/0.51    inference(avatar_component_clause,[],[f113])).
% 0.18/0.51  fof(f47,plain,(
% 0.18/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (29988)------------------------------
% 0.18/0.51  % (29988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (29988)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (29988)Memory used [KB]: 6524
% 0.18/0.51  % (29988)Time elapsed: 0.142 s
% 0.18/0.51  % (29988)------------------------------
% 0.18/0.51  % (29988)------------------------------
% 0.18/0.51  % (29989)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.51  % (29981)Success in time 0.176 s
%------------------------------------------------------------------------------
