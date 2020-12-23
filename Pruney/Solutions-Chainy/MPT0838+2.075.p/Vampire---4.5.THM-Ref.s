%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 222 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 ( 634 expanded)
%              Number of equality atoms :   25 ( 113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f60,f62,f77,f115,f117,f127,f131,f143,f157,f202])).

fof(f202,plain,
    ( ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl5_12
    | spl5_14 ),
    inference(resolution,[],[f172,f67])).

fof(f67,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f172,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl5_12
    | spl5_14 ),
    inference(resolution,[],[f130,f162])).

fof(f162,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl5_14 ),
    inference(resolution,[],[f155,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f155,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f130,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ v5_relat_1(sK2,X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_12
  <=> ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ v5_relat_1(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f157,plain,
    ( ~ spl5_14
    | ~ spl5_11
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f151,f125,f47,f125,f154])).

fof(f47,plain,
    ( spl5_2
  <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f125,plain,
    ( spl5_11
  <=> r2_hidden(sK4(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f151,plain,
    ( ~ r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f136,f126])).

fof(f126,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f120,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f91,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f83,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f91,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f27,f83])).

fof(f27,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_8 ),
    inference(superposition,[],[f86,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f104,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_8
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f86,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f29,f80])).

fof(f80,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f29,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( ~ spl5_3
    | spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f122,f47,f129,f55])).

fof(f55,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f122,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ v1_relat_1(sK2)
        | ~ v5_relat_1(sK2,X1) )
    | ~ spl5_2 ),
    inference(superposition,[],[f34,f118])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f127,plain,
    ( ~ spl5_3
    | spl5_8
    | spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f121,f47,f125,f103,f55])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f35,f118])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

fof(f117,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f114,f67])).

fof(f114,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_10
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f115,plain,
    ( ~ spl5_10
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f111,f75,f55,f113])).

fof(f75,plain,
    ( spl5_5
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | spl5_5 ),
    inference(resolution,[],[f87,f34])).

fof(f87,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_5 ),
    inference(backward_demodulation,[],[f78,f83])).

fof(f78,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)
    | spl5_5 ),
    inference(resolution,[],[f76,f36])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl5_2
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f73,f44,f75,f47])).

fof(f44,plain,
    ( spl5_1
  <=> m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f73,plain,
    ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | spl5_1 ),
    inference(resolution,[],[f69,f31])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_relset_1(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | spl5_1 ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,
    ( ~ m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f62,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f59,f32])).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f60,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f52,f58,f55])).

fof(f52,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f49,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f42,f47,f44])).

fof(f42,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f31,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (19145)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (19145)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f49,f60,f62,f77,f115,f117,f127,f131,f143,f157,f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ~spl5_12 | spl5_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    $false | (~spl5_12 | spl5_14)),
% 0.21/0.51    inference(resolution,[],[f172,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v5_relat_1(sK2,sK1)),
% 0.21/0.51    inference(resolution,[],[f40,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~v5_relat_1(sK2,sK1) | (~spl5_12 | spl5_14)),
% 0.21/0.51    inference(resolution,[],[f130,f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK1) | spl5_14),
% 0.21/0.51    inference(resolution,[],[f155,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl5_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~v5_relat_1(sK2,X1)) ) | ~spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl5_12 <=> ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~v5_relat_1(sK2,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~spl5_14 | ~spl5_11 | ~spl5_2 | ~spl5_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f151,f125,f47,f125,f154])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl5_2 <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl5_11 <=> r2_hidden(sK4(sK2),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK2),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | (~spl5_2 | ~spl5_11)),
% 0.21/0.51    inference(resolution,[],[f136,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    r2_hidden(sK4(sK2),k1_xboole_0) | ~spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,X1)) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f120,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_xboole_0)) ) | ~spl5_2),
% 0.21/0.51    inference(backward_demodulation,[],[f91,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_2),
% 0.21/0.51    inference(backward_demodulation,[],[f83,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f47])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f39,f28])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f27,f83])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~spl5_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    $false | ~spl5_8),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl5_8),
% 0.21/0.51    inference(superposition,[],[f86,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_8),
% 0.21/0.51    inference(resolution,[],[f104,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl5_8 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f29,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f38,f28])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~spl5_3 | spl5_12 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f47,f129,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl5_3 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X1)) ) | ~spl5_2),
% 0.21/0.51    inference(superposition,[],[f34,f118])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl5_3 | spl5_8 | spl5_11 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f121,f47,f125,f103,f55])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(sK2),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl5_2),
% 0.21/0.51    inference(superposition,[],[f35,f118])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl5_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    $false | spl5_10),
% 0.21/0.51    inference(resolution,[],[f114,f67])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~v5_relat_1(sK2,sK1) | spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl5_10 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ~spl5_10 | ~spl5_3 | spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f111,f75,f55,f113])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl5_5 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | spl5_5),
% 0.21/0.51    inference(resolution,[],[f87,f34])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_5),
% 0.21/0.51    inference(backward_demodulation,[],[f78,f83])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) | spl5_5),
% 0.21/0.51    inference(resolution,[],[f76,f36])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl5_2 | ~spl5_5 | spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f44,f75,f47])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl5_1 <=> m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | spl5_1),
% 0.21/0.51    inference(resolution,[],[f69,f31])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK3(k2_relset_1(sK0,sK1,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | spl5_1),
% 0.21/0.51    inference(resolution,[],[f41,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    $false | spl5_4),
% 0.21/0.51    inference(resolution,[],[f59,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl5_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl5_3 | ~spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f58,f55])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f30,f28])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~spl5_1 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f47,f44])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.21/0.51    inference(resolution,[],[f31,f27])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (19145)------------------------------
% 0.21/0.51  % (19145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19145)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (19145)Memory used [KB]: 10618
% 0.21/0.51  % (19145)Time elapsed: 0.089 s
% 0.21/0.51  % (19145)------------------------------
% 0.21/0.51  % (19145)------------------------------
% 0.21/0.51  % (19132)Success in time 0.148 s
%------------------------------------------------------------------------------
