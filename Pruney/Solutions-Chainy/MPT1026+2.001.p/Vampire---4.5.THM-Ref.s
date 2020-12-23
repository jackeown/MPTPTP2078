%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 460 expanded)
%              Number of leaves         :   21 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  333 (1413 expanded)
%              Number of equality atoms :   51 ( 318 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f841,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f181,f222,f452,f458,f654,f818,f840])).

fof(f840,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f115,f235,f234,f217,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f217,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl11_4
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f234,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl11_1
    | spl11_2 ),
    inference(backward_demodulation,[],[f120,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_1
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f125,f120,f191,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f191,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f182,f113])).

fof(f113,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f107,f106])).

fof(f106,plain,(
    sK2 = sK6(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f41,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( sK6(X0,X1,X3) = X3
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sK6(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f41,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f107,plain,(
    sK0 = k1_relat_1(sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(sK6(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK6(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f182,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f120,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f125,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl11_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f235,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl11_1
    | spl11_2 ),
    inference(backward_demodulation,[],[f125,f228])).

fof(f115,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f105,f106])).

fof(f105,plain,(
    v1_funct_1(sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( v1_funct_1(sK6(X0,X1,X3))
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK6(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f818,plain,(
    ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f817])).

fof(f817,plain,
    ( $false
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f78,f767,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f767,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f717,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f717,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f713,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f713,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f451,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f451,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl11_12
  <=> r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f654,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_5
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | spl11_5
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f221,f617,f62])).

fof(f617,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(forward_demodulation,[],[f609,f113])).

fof(f609,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f116,f115,f577,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f577,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f554,f63])).

fof(f554,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f495,f234,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f495,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f78,f447,f45])).

fof(f447,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl11_11
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f116,plain,(
    v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f104,f106])).

fof(f104,plain,(
    v1_relat_1(sK6(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( v1_relat_1(sK6(X0,X1,X3))
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK6(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK0)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl11_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f458,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f115,f129])).

fof(f129,plain,
    ( ~ v1_funct_1(sK2)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl11_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f452,plain,
    ( spl11_11
    | spl11_12
    | ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f342,f123,f119,f449,f445])).

fof(f342,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl11_1
    | spl11_2 ),
    inference(resolution,[],[f244,f62])).

fof(f244,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | r2_hidden(X1,k1_xboole_0) )
    | ~ spl11_1
    | spl11_2 ),
    inference(backward_demodulation,[],[f146,f228])).

fof(f146,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f114,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f114,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f108,f106])).

fof(f108,plain,(
    r1_tarski(k2_relat_1(sK6(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f41,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f222,plain,
    ( spl11_4
    | ~ spl11_5
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f186,f119,f219,f215])).

fof(f186,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0)
    | ~ spl11_1 ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f181,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f155,f157,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f157,plain,
    ( r2_hidden(sK3(sK0,sK0),sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f155,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f155,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl11_1 ),
    inference(forward_demodulation,[],[f151,f113])).

fof(f151,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f116,f114,f121,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f130,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f40,f127,f123,f119])).

fof(f40,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10926)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (10918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (10909)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (10908)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (10910)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (10912)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (10906)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (10925)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (10907)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (10917)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (10932)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (10919)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (10905)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (10924)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (10904)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10916)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (10931)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10925)Refutation not found, incomplete strategy% (10925)------------------------------
% 0.21/0.54  % (10925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10925)Memory used [KB]: 10746
% 0.21/0.54  % (10925)Time elapsed: 0.133 s
% 0.21/0.54  % (10925)------------------------------
% 0.21/0.54  % (10925)------------------------------
% 0.21/0.54  % (10911)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (10928)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10913)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (10913)Refutation not found, incomplete strategy% (10913)------------------------------
% 0.21/0.54  % (10913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10913)Memory used [KB]: 10746
% 0.21/0.54  % (10913)Time elapsed: 0.131 s
% 0.21/0.54  % (10913)------------------------------
% 0.21/0.54  % (10913)------------------------------
% 0.21/0.54  % (10903)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (10930)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10923)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (10914)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (10915)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (10929)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (10920)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (10922)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (10921)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (10907)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f841,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f130,f181,f222,f452,f458,f654,f818,f840])).
% 0.21/0.56  fof(f840,plain,(
% 0.21/0.56    ~spl11_1 | spl11_2 | ~spl11_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f836])).
% 0.21/0.56  fof(f836,plain,(
% 0.21/0.56    $false | (~spl11_1 | spl11_2 | ~spl11_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f115,f235,f234,f217,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    v1_partfun1(sK2,sK0) | ~spl11_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f215])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    spl11_4 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.56  fof(f234,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl11_1 | spl11_2)),
% 0.21/0.56    inference(backward_demodulation,[],[f120,f228])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | (~spl11_1 | spl11_2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f125,f120,f191,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl11_1),
% 0.21/0.56    inference(forward_demodulation,[],[f182,f113])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f107,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    sK2 = sK6(sK0,sK1,sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f41,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (sK6(X0,X1,X3) = X3 | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sK6(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(negated_conjecture,[],[f19])).
% 0.21/0.56  fof(f19,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK6(sK0,sK1,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f41,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (k1_relat_1(sK6(X0,X1,X3)) = X0 | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK6(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl11_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f120,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    ~v1_funct_2(sK2,sK0,sK1) | spl11_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    spl11_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f119])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    spl11_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl11_1 | spl11_2)),
% 0.21/0.56    inference(backward_demodulation,[],[f125,f228])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f105,f106])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    v1_funct_1(sK6(sK0,sK1,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f41,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (v1_funct_1(sK6(X0,X1,X3)) | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK6(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f818,plain,(
% 0.21/0.56    ~spl11_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f817])).
% 0.21/0.56  fof(f817,plain,(
% 0.21/0.56    $false | ~spl11_12),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f78,f767,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f767,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK4(k1_xboole_0)) | ~spl11_12),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f717,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.56  fof(f717,plain,(
% 0.21/0.56    r2_hidden(sK4(k1_xboole_0),k1_xboole_0) | ~spl11_12),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f713,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f713,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl11_12),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f451,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f451,plain,(
% 0.21/0.56    r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0) | ~spl11_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f449])).
% 0.21/0.56  fof(f449,plain,(
% 0.21/0.56    spl11_12 <=> r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f654,plain,(
% 0.21/0.56    ~spl11_1 | spl11_2 | spl11_5 | ~spl11_11),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f647])).
% 0.21/0.56  fof(f647,plain,(
% 0.21/0.56    $false | (~spl11_1 | spl11_2 | spl11_5 | ~spl11_11)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f221,f617,f62])).
% 0.21/0.56  fof(f617,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.21/0.56    inference(forward_demodulation,[],[f609,f113])).
% 0.21/0.56  fof(f609,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f116,f115,f577,f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.56  fof(f577,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f554,f63])).
% 0.21/0.56  fof(f554,plain,(
% 0.21/0.56    v1_xboole_0(sK2) | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f495,f234,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.56  fof(f495,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0) | ~spl11_11),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f78,f447,f45])).
% 0.21/0.56  fof(f447,plain,(
% 0.21/0.56    v1_xboole_0(k2_relat_1(sK2)) | ~spl11_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f445])).
% 0.21/0.56  fof(f445,plain,(
% 0.21/0.56    spl11_11 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f104,f106])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    v1_relat_1(sK6(sK0,sK1,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f41,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (v1_relat_1(sK6(X0,X1,X3)) | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK6(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ~v1_xboole_0(sK0) | spl11_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f219])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    spl11_5 <=> v1_xboole_0(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.56  fof(f458,plain,(
% 0.21/0.56    spl11_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f453])).
% 0.21/0.56  fof(f453,plain,(
% 0.21/0.56    $false | spl11_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f115,f129])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | spl11_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    spl11_3 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.56  fof(f452,plain,(
% 0.21/0.56    spl11_11 | spl11_12 | ~spl11_1 | spl11_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f342,f123,f119,f449,f445])).
% 0.21/0.56  fof(f342,plain,(
% 0.21/0.56    r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0) | v1_xboole_0(k2_relat_1(sK2)) | (~spl11_1 | spl11_2)),
% 0.21/0.56    inference(resolution,[],[f244,f62])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | r2_hidden(X1,k1_xboole_0)) ) | (~spl11_1 | spl11_2)),
% 0.21/0.56    inference(backward_demodulation,[],[f146,f228])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,k2_relat_1(sK2))) )),
% 0.21/0.56    inference(resolution,[],[f114,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.56    inference(backward_demodulation,[],[f108,f106])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    r1_tarski(k2_relat_1(sK6(sK0,sK1,sK2)),sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f41,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    spl11_4 | ~spl11_5 | ~spl11_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f186,f119,f219,f215])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0) | ~spl11_1),
% 0.21/0.56    inference(resolution,[],[f120,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    spl11_1),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f176])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    $false | spl11_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f155,f157,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    r2_hidden(sK3(sK0,sK0),sK0) | spl11_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f155,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ~r1_tarski(sK0,sK0) | spl11_1),
% 0.21/0.56    inference(forward_demodulation,[],[f151,f113])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | spl11_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f116,f114,f121,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl11_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f119])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    ~spl11_1 | ~spl11_2 | ~spl11_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f40,f127,f123,f119])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (10907)------------------------------
% 0.21/0.56  % (10907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10907)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (10907)Memory used [KB]: 6524
% 0.21/0.56  % (10907)Time elapsed: 0.138 s
% 0.21/0.56  % (10907)------------------------------
% 0.21/0.56  % (10907)------------------------------
% 0.21/0.57  % (10902)Success in time 0.203 s
%------------------------------------------------------------------------------
