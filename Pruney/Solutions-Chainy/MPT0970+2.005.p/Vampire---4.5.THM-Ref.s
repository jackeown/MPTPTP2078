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
% DateTime   : Thu Dec  3 13:00:49 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 283 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (1066 expanded)
%              Number of equality atoms :   60 ( 264 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f238,f246,f293,f446,f650,f685])).

fof(f685,plain,(
    ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f106,f113,f109,f649])).

fof(f649,plain,
    ( ! [X2] :
        ( r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))
        | r1_tarski(sK1,X2)
        | ~ r2_hidden(sK3(sK7(sK1,X2)),sK0) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl8_17
  <=> ! [X2] :
        ( ~ r2_hidden(sK3(sK7(sK1,X2)),sK0)
        | r1_tarski(sK1,X2)
        | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f109,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f113,plain,(
    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f108,f28])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f108,plain,(
    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f91,f102,f37])).

fof(f37,plain,(
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

fof(f102,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f33,f77])).

fof(f77,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f78,f81,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f81,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f32,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f650,plain,
    ( ~ spl8_2
    | ~ spl8_10
    | spl8_17
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f421,f235,f648,f436,f168])).

fof(f168,plain,
    ( spl8_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f436,plain,
    ( spl8_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f235,plain,
    ( spl8_9
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f421,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK7(sK1,X2)),sK0)
        | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK1,X2) )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f419,f237])).

fof(f237,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f235])).

fof(f419,plain,(
    ! [X2] :
      ( r2_hidden(sK7(sK1,X2),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(sK7(sK1,X2)),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f66,f104])).

fof(f104,plain,(
    ! [X2] :
      ( sK7(sK1,X2) = k1_funct_1(sK2,sK3(sK7(sK1,X2)))
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f29,f46])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
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

fof(f446,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f30,f438])).

fof(f438,plain,
    ( ~ v1_funct_1(sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f436])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f293,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f64,f268])).

fof(f268,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f118,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f118,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f60,f108,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f246,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f82,f229,f48])).

fof(f229,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f82,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f238,plain,
    ( ~ spl8_7
    | spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f87,f235,f231,f227])).

fof(f87,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f76,f79])).

fof(f79,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f32,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f31,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f179,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f32,f170,f50])).

fof(f170,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (7337)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (7346)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (7328)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (7331)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7341)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (7329)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.53  % (7333)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (7350)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.53  % (7330)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.53  % (7343)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.53  % (7357)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (7338)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (7342)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (7339)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (7338)Refutation not found, incomplete strategy% (7338)------------------------------
% 1.35/0.54  % (7338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (7338)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (7338)Memory used [KB]: 10746
% 1.35/0.54  % (7338)Time elapsed: 0.132 s
% 1.35/0.54  % (7338)------------------------------
% 1.35/0.54  % (7338)------------------------------
% 1.35/0.54  % (7347)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (7355)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (7354)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (7356)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (7334)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (7332)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (7351)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (7335)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.55  % (7348)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.55  % (7336)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (7345)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.56  % (7349)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.56  % (7344)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.56  % (7353)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.57  % (7340)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.58  % (7352)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.58  % (7345)Refutation not found, incomplete strategy% (7345)------------------------------
% 1.49/0.58  % (7345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (7345)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (7345)Memory used [KB]: 10746
% 1.49/0.58  % (7345)Time elapsed: 0.178 s
% 1.49/0.58  % (7345)------------------------------
% 1.49/0.58  % (7345)------------------------------
% 1.49/0.59  % (7332)Refutation found. Thanks to Tanya!
% 1.49/0.59  % SZS status Theorem for theBenchmark
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f686,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(avatar_sat_refutation,[],[f179,f238,f246,f293,f446,f650,f685])).
% 1.49/0.59  fof(f685,plain,(
% 1.49/0.59    ~spl8_17),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f679])).
% 1.49/0.59  fof(f679,plain,(
% 1.49/0.59    $false | ~spl8_17),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f106,f113,f109,f649])).
% 1.49/0.59  fof(f649,plain,(
% 1.49/0.59    ( ! [X2] : (r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) | r1_tarski(sK1,X2) | ~r2_hidden(sK3(sK7(sK1,X2)),sK0)) ) | ~spl8_17),
% 1.49/0.59    inference(avatar_component_clause,[],[f648])).
% 1.49/0.59  fof(f648,plain,(
% 1.49/0.59    spl8_17 <=> ! [X2] : (~r2_hidden(sK3(sK7(sK1,X2)),sK0) | r1_tarski(sK1,X2) | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.49/0.59  fof(f109,plain,(
% 1.49/0.59    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f106,f47])).
% 1.49/0.59  fof(f47,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.59  fof(f113,plain,(
% 1.49/0.59    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f108,f28])).
% 1.49/0.59  fof(f28,plain,(
% 1.49/0.59    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f16,plain,(
% 1.49/0.59    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.49/0.59    inference(flattening,[],[f15])).
% 1.49/0.59  fof(f15,plain,(
% 1.49/0.59    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.49/0.59    inference(ennf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,negated_conjecture,(
% 1.49/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.49/0.59    inference(negated_conjecture,[],[f13])).
% 1.49/0.59  fof(f13,conjecture,(
% 1.49/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.49/0.59  fof(f108,plain,(
% 1.49/0.59    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f106,f46])).
% 1.49/0.59  fof(f46,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f106,plain,(
% 1.49/0.59    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f91,f102,f37])).
% 1.49/0.59  fof(f37,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f3])).
% 1.49/0.59  fof(f3,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f102,plain,(
% 1.49/0.59    sK1 != k2_relat_1(sK2)),
% 1.49/0.59    inference(superposition,[],[f33,f77])).
% 1.49/0.59  fof(f77,plain,(
% 1.49/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f34])).
% 1.49/0.59  fof(f34,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f17])).
% 1.49/0.59  fof(f17,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.59    inference(ennf_transformation,[],[f11])).
% 1.49/0.59  fof(f11,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.49/0.59  fof(f32,plain,(
% 1.49/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f33,plain,(
% 1.49/0.59    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f91,plain,(
% 1.49/0.59    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f78,f81,f58])).
% 1.49/0.59  fof(f58,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f25])).
% 1.49/0.59  fof(f25,plain,(
% 1.49/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.49/0.59  fof(f81,plain,(
% 1.49/0.59    v5_relat_1(sK2,sK1)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f62])).
% 1.49/0.59  fof(f62,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f27])).
% 1.49/0.59  fof(f27,plain,(
% 1.49/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.59    inference(ennf_transformation,[],[f9])).
% 1.49/0.59  fof(f9,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.59  fof(f78,plain,(
% 1.49/0.59    v1_relat_1(sK2)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f50])).
% 1.49/0.59  fof(f50,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f22])).
% 1.49/0.59  fof(f22,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.59    inference(ennf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.59  fof(f650,plain,(
% 1.49/0.59    ~spl8_2 | ~spl8_10 | spl8_17 | ~spl8_9),
% 1.49/0.59    inference(avatar_split_clause,[],[f421,f235,f648,f436,f168])).
% 1.49/0.59  fof(f168,plain,(
% 1.49/0.59    spl8_2 <=> v1_relat_1(sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.49/0.59  fof(f436,plain,(
% 1.49/0.59    spl8_10 <=> v1_funct_1(sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.49/0.59  fof(f235,plain,(
% 1.49/0.59    spl8_9 <=> sK0 = k1_relat_1(sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.49/0.59  fof(f421,plain,(
% 1.49/0.59    ( ! [X2] : (~r2_hidden(sK3(sK7(sK1,X2)),sK0) | r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(sK1,X2)) ) | ~spl8_9),
% 1.49/0.59    inference(forward_demodulation,[],[f419,f237])).
% 1.49/0.59  fof(f237,plain,(
% 1.49/0.59    sK0 = k1_relat_1(sK2) | ~spl8_9),
% 1.49/0.59    inference(avatar_component_clause,[],[f235])).
% 1.49/0.59  fof(f419,plain,(
% 1.49/0.59    ( ! [X2] : (r2_hidden(sK7(sK1,X2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(sK7(sK1,X2)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_tarski(sK1,X2)) )),
% 1.49/0.59    inference(superposition,[],[f66,f104])).
% 1.49/0.59  fof(f104,plain,(
% 1.49/0.59    ( ! [X2] : (sK7(sK1,X2) = k1_funct_1(sK2,sK3(sK7(sK1,X2))) | r1_tarski(sK1,X2)) )),
% 1.49/0.59    inference(resolution,[],[f29,f46])).
% 1.49/0.59  fof(f29,plain,(
% 1.49/0.59    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f66,plain,(
% 1.49/0.59    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(equality_resolution,[],[f65])).
% 1.49/0.59  fof(f65,plain,(
% 1.49/0.59    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.49/0.59    inference(equality_resolution,[],[f43])).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f19])).
% 1.49/0.59  fof(f19,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.59    inference(flattening,[],[f18])).
% 1.49/0.59  fof(f18,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f7])).
% 1.49/0.59  fof(f7,axiom,(
% 1.49/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.49/0.59  fof(f446,plain,(
% 1.49/0.59    spl8_10),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f443])).
% 1.49/0.59  fof(f443,plain,(
% 1.49/0.59    $false | spl8_10),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f30,f438])).
% 1.49/0.59  fof(f438,plain,(
% 1.49/0.59    ~v1_funct_1(sK2) | spl8_10),
% 1.49/0.59    inference(avatar_component_clause,[],[f436])).
% 1.49/0.59  fof(f30,plain,(
% 1.49/0.59    v1_funct_1(sK2)),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f293,plain,(
% 1.49/0.59    ~spl8_8),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f285])).
% 1.49/0.59  fof(f285,plain,(
% 1.49/0.59    $false | ~spl8_8),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f64,f268])).
% 1.49/0.59  fof(f268,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl8_8),
% 1.49/0.59    inference(backward_demodulation,[],[f118,f233])).
% 1.49/0.59  fof(f233,plain,(
% 1.49/0.59    k1_xboole_0 = sK1 | ~spl8_8),
% 1.49/0.59    inference(avatar_component_clause,[],[f231])).
% 1.49/0.59  fof(f231,plain,(
% 1.49/0.59    spl8_8 <=> k1_xboole_0 = sK1),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.49/0.59  fof(f118,plain,(
% 1.49/0.59    ~r1_tarski(sK1,k1_xboole_0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f116,f48])).
% 1.49/0.59  fof(f48,plain,(
% 1.49/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.59  fof(f116,plain,(
% 1.49/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f60,f108,f44])).
% 1.49/0.59  fof(f44,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f20])).
% 1.49/0.59  fof(f20,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f5])).
% 1.49/0.59  fof(f5,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.49/0.60  fof(f60,plain,(
% 1.49/0.60    v1_xboole_0(k1_xboole_0)),
% 1.49/0.60    inference(cnf_transformation,[],[f2])).
% 1.49/0.60  fof(f2,axiom,(
% 1.49/0.60    v1_xboole_0(k1_xboole_0)),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.49/0.60  fof(f64,plain,(
% 1.49/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.60    inference(equality_resolution,[],[f35])).
% 1.49/0.60  fof(f35,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.49/0.60    inference(cnf_transformation,[],[f3])).
% 1.49/0.60  fof(f246,plain,(
% 1.49/0.60    spl8_7),
% 1.49/0.60    inference(avatar_contradiction_clause,[],[f241])).
% 1.49/0.60  fof(f241,plain,(
% 1.49/0.60    $false | spl8_7),
% 1.49/0.60    inference(unit_resulting_resolution,[],[f82,f229,f48])).
% 1.49/0.60  fof(f229,plain,(
% 1.49/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_7),
% 1.49/0.60    inference(avatar_component_clause,[],[f227])).
% 1.49/0.60  fof(f227,plain,(
% 1.49/0.60    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.49/0.60  fof(f82,plain,(
% 1.49/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.49/0.60    inference(unit_resulting_resolution,[],[f32,f49])).
% 1.49/0.60  fof(f49,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f4])).
% 1.49/0.60  fof(f238,plain,(
% 1.49/0.60    ~spl8_7 | spl8_8 | spl8_9),
% 1.49/0.60    inference(avatar_split_clause,[],[f87,f235,f231,f227])).
% 1.49/0.60  fof(f87,plain,(
% 1.49/0.60    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.60    inference(backward_demodulation,[],[f76,f79])).
% 1.49/0.60  fof(f79,plain,(
% 1.49/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.49/0.60    inference(unit_resulting_resolution,[],[f32,f59])).
% 1.49/0.60  fof(f59,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f26])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(ennf_transformation,[],[f10])).
% 1.49/0.60  fof(f10,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.60  fof(f76,plain,(
% 1.49/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.60    inference(resolution,[],[f31,f56])).
% 1.49/0.60  fof(f56,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f24])).
% 1.49/0.60  fof(f24,plain,(
% 1.49/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(flattening,[],[f23])).
% 1.49/0.60  fof(f23,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(ennf_transformation,[],[f12])).
% 1.49/0.60  fof(f12,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.49/0.60  fof(f31,plain,(
% 1.49/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.49/0.60    inference(cnf_transformation,[],[f16])).
% 1.49/0.60  fof(f179,plain,(
% 1.49/0.60    spl8_2),
% 1.49/0.60    inference(avatar_contradiction_clause,[],[f174])).
% 1.49/0.60  fof(f174,plain,(
% 1.49/0.60    $false | spl8_2),
% 1.49/0.60    inference(unit_resulting_resolution,[],[f32,f170,f50])).
% 1.49/0.60  fof(f170,plain,(
% 1.49/0.60    ~v1_relat_1(sK2) | spl8_2),
% 1.49/0.60    inference(avatar_component_clause,[],[f168])).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (7332)------------------------------
% 1.49/0.60  % (7332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (7332)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (7332)Memory used [KB]: 6524
% 1.49/0.60  % (7332)Time elapsed: 0.190 s
% 1.49/0.60  % (7332)------------------------------
% 1.49/0.60  % (7332)------------------------------
% 1.49/0.60  % (7327)Success in time 0.243 s
%------------------------------------------------------------------------------
