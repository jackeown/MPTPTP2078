%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:23 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 221 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          :  370 ( 661 expanded)
%              Number of equality atoms :   84 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f120,f122,f126,f171,f178,f192,f346,f509,f598,f607,f612,f633,f661,f687,f873,f881])).

fof(f881,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f873,plain,
    ( spl5_80
    | ~ spl5_34
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f869,f685,f456,f871])).

fof(f871,plain,
    ( spl5_80
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f456,plain,
    ( spl5_34
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f685,plain,
    ( spl5_64
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f869,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_34
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f859,f686])).

fof(f686,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f685])).

fof(f859,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl5_34 ),
    inference(resolution,[],[f660,f239])).

fof(f239,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f81,f149])).

fof(f149,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f72,f139])).

fof(f139,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f73,f63])).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f660,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f456])).

fof(f687,plain,
    ( spl5_64
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f679,f630,f685])).

fof(f630,plain,
    ( spl5_59
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f679,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_59 ),
    inference(resolution,[],[f631,f239])).

fof(f631,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f630])).

fof(f661,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f646,f593,f118,f456])).

fof(f118,plain,
    ( spl5_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f593,plain,
    ( spl5_51
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f646,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_51 ),
    inference(superposition,[],[f119,f594])).

fof(f594,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f593])).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f633,plain,
    ( ~ spl5_34
    | spl5_59
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f479,f124,f630,f456])).

fof(f124,plain,
    ( spl5_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f479,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl5_5 ),
    inference(superposition,[],[f473,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f473,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),X1))
        | ~ r1_tarski(k2_relat_1(sK1),X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f452,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK1),X1)
        | r1_tarski(sK1,k2_zfmisc_1(X0,X1)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f447,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f447,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK1),X1)
        | ~ r1_tarski(k2_relat_1(sK1),X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f90,f125])).

fof(f125,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f612,plain,
    ( ~ spl5_3
    | spl5_52 ),
    inference(avatar_split_clause,[],[f610,f596,f114])).

fof(f114,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f596,plain,
    ( spl5_52
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f610,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_52 ),
    inference(trivial_inequality_removal,[],[f609])).

fof(f609,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_52 ),
    inference(superposition,[],[f597,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f597,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl5_52 ),
    inference(avatar_component_clause,[],[f596])).

fof(f607,plain,
    ( ~ spl5_40
    | spl5_3 ),
    inference(avatar_split_clause,[],[f600,f114,f506])).

fof(f506,plain,
    ( spl5_40
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f600,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | spl5_3 ),
    inference(resolution,[],[f115,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f598,plain,
    ( ~ spl5_3
    | spl5_51
    | ~ spl5_52
    | spl5_2 ),
    inference(avatar_split_clause,[],[f590,f111,f596,f593,f114])).

fof(f111,plain,
    ( spl5_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f590,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_2 ),
    inference(resolution,[],[f94,f112])).

fof(f112,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f509,plain,
    ( spl5_40
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f499,f124,f118,f506])).

fof(f499,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(superposition,[],[f484,f63])).

fof(f484,plain,
    ( ! [X0] : r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK1),X0),sK0))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f474,f119])).

fof(f474,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_relat_1(sK1),X2)
        | r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK1),X3),X2)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f452,f72])).

fof(f346,plain,
    ( ~ spl5_5
    | spl5_28
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f341,f108,f344,f124])).

fof(f344,plain,
    ( spl5_28
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f108,plain,
    ( spl5_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f341,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f68,f121])).

fof(f121,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f192,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f184,f176,f190])).

fof(f190,plain,
    ( spl5_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f176,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f184,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(resolution,[],[f177,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f177,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f173,f168,f176])).

fof(f168,plain,
    ( spl5_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f173,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_9 ),
    inference(resolution,[],[f169,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f169,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f171,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f166,f168])).

fof(f166,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f164,f149])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f77,f62])).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f126,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f58,f124])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f122,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f59,f108])).

fof(f59,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f60,f118])).

fof(f60,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f61,f114,f111,f108])).

fof(f61,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.10/0.32  % Computer   : n006.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 18:34:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.18/0.48  % (17491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.48  % (17511)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.49  % (17507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.49  % (17503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.49  % (17515)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.49  % (17495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.49  % (17489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.50  % (17505)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.51  % (17508)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.51  % (17517)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.51  % (17488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.51  % (17500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (17488)Refutation not found, incomplete strategy% (17488)------------------------------
% 0.18/0.51  % (17488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (17488)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (17488)Memory used [KB]: 1663
% 0.18/0.51  % (17488)Time elapsed: 0.125 s
% 0.18/0.51  % (17488)------------------------------
% 0.18/0.51  % (17488)------------------------------
% 0.18/0.51  % (17513)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.51  % (17496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.52  % (17518)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.52  % (17504)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.52  % (17505)Refutation not found, incomplete strategy% (17505)------------------------------
% 1.38/0.52  % (17505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.52  % (17505)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.52  
% 1.38/0.52  % (17505)Memory used [KB]: 10618
% 1.38/0.52  % (17505)Time elapsed: 0.141 s
% 1.38/0.52  % (17505)------------------------------
% 1.38/0.52  % (17505)------------------------------
% 1.38/0.52  % (17492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.52  % (17497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.52  % (17490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.52  % (17507)Refutation found. Thanks to Tanya!
% 1.38/0.52  % SZS status Theorem for theBenchmark
% 1.38/0.52  % SZS output start Proof for theBenchmark
% 1.38/0.52  fof(f882,plain,(
% 1.38/0.52    $false),
% 1.38/0.52    inference(avatar_sat_refutation,[],[f116,f120,f122,f126,f171,f178,f192,f346,f509,f598,f607,f612,f633,f661,f687,f873,f881])).
% 1.38/0.52  fof(f881,plain,(
% 1.38/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | k1_xboole_0 != k2_relat_1(k1_xboole_0) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))),
% 1.38/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.38/0.52  fof(f873,plain,(
% 1.38/0.52    spl5_80 | ~spl5_34 | ~spl5_64),
% 1.38/0.52    inference(avatar_split_clause,[],[f869,f685,f456,f871])).
% 1.38/0.52  fof(f871,plain,(
% 1.38/0.52    spl5_80 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 1.38/0.52  fof(f456,plain,(
% 1.38/0.52    spl5_34 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.38/0.52  fof(f685,plain,(
% 1.38/0.52    spl5_64 <=> k1_xboole_0 = sK1),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 1.38/0.52  fof(f869,plain,(
% 1.38/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_34 | ~spl5_64)),
% 1.38/0.52    inference(forward_demodulation,[],[f859,f686])).
% 1.38/0.52  fof(f686,plain,(
% 1.38/0.52    k1_xboole_0 = sK1 | ~spl5_64),
% 1.38/0.52    inference(avatar_component_clause,[],[f685])).
% 1.38/0.52  fof(f859,plain,(
% 1.38/0.52    k1_xboole_0 = k2_relat_1(sK1) | ~spl5_34),
% 1.38/0.52    inference(resolution,[],[f660,f239])).
% 1.38/0.52  fof(f239,plain,(
% 1.38/0.52    ( ! [X5] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X5) )),
% 1.38/0.52    inference(resolution,[],[f81,f149])).
% 1.38/0.52  fof(f149,plain,(
% 1.38/0.52    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.38/0.52    inference(superposition,[],[f72,f139])).
% 1.38/0.52  fof(f139,plain,(
% 1.38/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.38/0.52    inference(superposition,[],[f73,f63])).
% 1.38/0.52  fof(f63,plain,(
% 1.38/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.52    inference(cnf_transformation,[],[f8])).
% 1.38/0.52  fof(f8,axiom,(
% 1.38/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.38/0.52  fof(f73,plain,(
% 1.38/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f1])).
% 1.38/0.52  fof(f1,axiom,(
% 1.38/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.38/0.52  fof(f72,plain,(
% 1.38/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.52    inference(cnf_transformation,[],[f11])).
% 1.38/0.52  fof(f11,axiom,(
% 1.38/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.38/0.52  fof(f81,plain,(
% 1.38/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f49])).
% 1.38/0.52  fof(f49,plain,(
% 1.38/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.52    inference(flattening,[],[f48])).
% 1.38/0.52  fof(f48,plain,(
% 1.38/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.52    inference(nnf_transformation,[],[f6])).
% 1.38/0.52  fof(f6,axiom,(
% 1.38/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.52  fof(f660,plain,(
% 1.38/0.52    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl5_34),
% 1.38/0.52    inference(avatar_component_clause,[],[f456])).
% 1.38/0.52  fof(f687,plain,(
% 1.38/0.52    spl5_64 | ~spl5_59),
% 1.38/0.52    inference(avatar_split_clause,[],[f679,f630,f685])).
% 1.38/0.52  fof(f630,plain,(
% 1.38/0.52    spl5_59 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 1.38/0.52  fof(f679,plain,(
% 1.38/0.52    k1_xboole_0 = sK1 | ~spl5_59),
% 1.38/0.52    inference(resolution,[],[f631,f239])).
% 1.38/0.52  fof(f631,plain,(
% 1.38/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl5_59),
% 1.38/0.52    inference(avatar_component_clause,[],[f630])).
% 1.38/0.52  fof(f661,plain,(
% 1.38/0.52    spl5_34 | ~spl5_4 | ~spl5_51),
% 1.38/0.52    inference(avatar_split_clause,[],[f646,f593,f118,f456])).
% 1.38/0.52  fof(f118,plain,(
% 1.38/0.52    spl5_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.38/0.52  fof(f593,plain,(
% 1.38/0.52    spl5_51 <=> k1_xboole_0 = sK0),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.38/0.52  fof(f646,plain,(
% 1.38/0.52    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl5_4 | ~spl5_51)),
% 1.38/0.52    inference(superposition,[],[f119,f594])).
% 1.38/0.52  fof(f594,plain,(
% 1.38/0.52    k1_xboole_0 = sK0 | ~spl5_51),
% 1.38/0.52    inference(avatar_component_clause,[],[f593])).
% 1.38/0.52  fof(f119,plain,(
% 1.38/0.52    r1_tarski(k2_relat_1(sK1),sK0) | ~spl5_4),
% 1.38/0.52    inference(avatar_component_clause,[],[f118])).
% 1.38/0.52  fof(f633,plain,(
% 1.38/0.52    ~spl5_34 | spl5_59 | ~spl5_5),
% 1.38/0.52    inference(avatar_split_clause,[],[f479,f124,f630,f456])).
% 1.38/0.52  fof(f124,plain,(
% 1.38/0.52    spl5_5 <=> v1_relat_1(sK1)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.38/0.52  fof(f479,plain,(
% 1.38/0.52    r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl5_5),
% 1.38/0.52    inference(superposition,[],[f473,f100])).
% 1.38/0.52  fof(f100,plain,(
% 1.38/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.38/0.52    inference(equality_resolution,[],[f89])).
% 1.38/0.52  fof(f89,plain,(
% 1.38/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.38/0.52    inference(cnf_transformation,[],[f56])).
% 1.38/0.52  fof(f56,plain,(
% 1.38/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.38/0.52    inference(flattening,[],[f55])).
% 1.38/0.52  fof(f55,plain,(
% 1.38/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.38/0.52    inference(nnf_transformation,[],[f12])).
% 1.38/0.52  fof(f12,axiom,(
% 1.38/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.38/0.52  fof(f473,plain,(
% 1.38/0.52    ( ! [X1] : (r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),X1)) | ~r1_tarski(k2_relat_1(sK1),X1)) ) | ~spl5_5),
% 1.38/0.52    inference(resolution,[],[f452,f98])).
% 1.38/0.52  fof(f98,plain,(
% 1.38/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.52    inference(equality_resolution,[],[f80])).
% 1.38/0.52  fof(f80,plain,(
% 1.38/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.52    inference(cnf_transformation,[],[f49])).
% 1.38/0.52  fof(f452,plain,(
% 1.38/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK1),X1) | r1_tarski(sK1,k2_zfmisc_1(X0,X1))) ) | ~spl5_5),
% 1.38/0.52    inference(resolution,[],[f447,f85])).
% 1.38/0.52  fof(f85,plain,(
% 1.38/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f54])).
% 1.38/0.52  fof(f54,plain,(
% 1.38/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.52    inference(nnf_transformation,[],[f13])).
% 1.38/0.52  fof(f13,axiom,(
% 1.38/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.52  fof(f447,plain,(
% 1.38/0.52    ( ! [X0,X1] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK1),X1) | ~r1_tarski(k2_relat_1(sK1),X0)) ) | ~spl5_5),
% 1.38/0.52    inference(resolution,[],[f90,f125])).
% 1.38/0.52  fof(f125,plain,(
% 1.38/0.52    v1_relat_1(sK1) | ~spl5_5),
% 1.38/0.52    inference(avatar_component_clause,[],[f124])).
% 1.38/0.52  fof(f90,plain,(
% 1.38/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.52    inference(cnf_transformation,[],[f36])).
% 1.38/0.52  fof(f36,plain,(
% 1.38/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.38/0.52    inference(flattening,[],[f35])).
% 1.38/0.52  fof(f35,plain,(
% 1.38/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.38/0.52    inference(ennf_transformation,[],[f17])).
% 1.38/0.52  fof(f17,axiom,(
% 1.38/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.38/0.52  fof(f612,plain,(
% 1.38/0.52    ~spl5_3 | spl5_52),
% 1.38/0.52    inference(avatar_split_clause,[],[f610,f596,f114])).
% 1.38/0.52  fof(f114,plain,(
% 1.38/0.52    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.38/0.52  fof(f596,plain,(
% 1.38/0.52    spl5_52 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.38/0.52  fof(f610,plain,(
% 1.38/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl5_52),
% 1.38/0.52    inference(trivial_inequality_removal,[],[f609])).
% 1.38/0.52  fof(f609,plain,(
% 1.38/0.52    k1_relat_1(sK1) != k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl5_52),
% 1.38/0.52    inference(superposition,[],[f597,f91])).
% 1.38/0.52  fof(f91,plain,(
% 1.38/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.52    inference(cnf_transformation,[],[f37])).
% 1.38/0.52  fof(f37,plain,(
% 1.38/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.52    inference(ennf_transformation,[],[f16])).
% 1.38/0.52  fof(f16,axiom,(
% 1.38/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.52  fof(f597,plain,(
% 1.38/0.52    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | spl5_52),
% 1.38/0.52    inference(avatar_component_clause,[],[f596])).
% 1.38/0.52  fof(f607,plain,(
% 1.38/0.52    ~spl5_40 | spl5_3),
% 1.38/0.52    inference(avatar_split_clause,[],[f600,f114,f506])).
% 1.38/0.52  fof(f506,plain,(
% 1.38/0.52    spl5_40 <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.38/0.52  fof(f600,plain,(
% 1.38/0.52    ~r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | spl5_3),
% 1.38/0.52    inference(resolution,[],[f115,f86])).
% 1.38/0.52  fof(f86,plain,(
% 1.38/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f54])).
% 1.38/0.52  fof(f115,plain,(
% 1.38/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl5_3),
% 1.38/0.52    inference(avatar_component_clause,[],[f114])).
% 1.38/0.52  fof(f598,plain,(
% 1.38/0.52    ~spl5_3 | spl5_51 | ~spl5_52 | spl5_2),
% 1.38/0.52    inference(avatar_split_clause,[],[f590,f111,f596,f593,f114])).
% 1.38/0.52  fof(f111,plain,(
% 1.38/0.52    spl5_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.38/0.52  fof(f590,plain,(
% 1.38/0.52    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl5_2),
% 1.38/0.52    inference(resolution,[],[f94,f112])).
% 1.38/0.52  fof(f112,plain,(
% 1.38/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl5_2),
% 1.38/0.52    inference(avatar_component_clause,[],[f111])).
% 1.38/0.52  fof(f94,plain,(
% 1.38/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.52    inference(cnf_transformation,[],[f57])).
% 1.38/0.52  fof(f57,plain,(
% 1.38/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.52    inference(nnf_transformation,[],[f39])).
% 1.38/0.52  fof(f39,plain,(
% 1.38/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.52    inference(flattening,[],[f38])).
% 1.38/0.52  fof(f38,plain,(
% 1.38/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.52    inference(ennf_transformation,[],[f18])).
% 1.38/0.52  fof(f18,axiom,(
% 1.38/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.38/0.52  fof(f509,plain,(
% 1.38/0.52    spl5_40 | ~spl5_4 | ~spl5_5),
% 1.38/0.52    inference(avatar_split_clause,[],[f499,f124,f118,f506])).
% 1.38/0.52  fof(f499,plain,(
% 1.38/0.52    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | (~spl5_4 | ~spl5_5)),
% 1.38/0.52    inference(superposition,[],[f484,f63])).
% 1.38/0.52  fof(f484,plain,(
% 1.38/0.52    ( ! [X0] : (r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK1),X0),sK0))) ) | (~spl5_4 | ~spl5_5)),
% 1.38/0.52    inference(resolution,[],[f474,f119])).
% 1.38/0.52  fof(f474,plain,(
% 1.38/0.52    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(sK1),X2) | r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK1),X3),X2))) ) | ~spl5_5),
% 1.38/0.52    inference(resolution,[],[f452,f72])).
% 1.38/0.52  fof(f346,plain,(
% 1.38/0.52    ~spl5_5 | spl5_28 | ~spl5_1),
% 1.38/0.52    inference(avatar_split_clause,[],[f341,f108,f344,f124])).
% 1.38/0.52  fof(f344,plain,(
% 1.38/0.52    spl5_28 <=> v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.38/0.52  fof(f108,plain,(
% 1.38/0.52    spl5_1 <=> v1_funct_1(sK1)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.38/0.52  fof(f341,plain,(
% 1.38/0.52    v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl5_1),
% 1.38/0.52    inference(resolution,[],[f68,f121])).
% 1.38/0.52  fof(f121,plain,(
% 1.38/0.52    v1_funct_1(sK1) | ~spl5_1),
% 1.38/0.52    inference(avatar_component_clause,[],[f108])).
% 1.38/0.52  fof(f68,plain,(
% 1.38/0.52    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f29])).
% 1.38/0.52  fof(f29,plain,(
% 1.38/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.52    inference(flattening,[],[f28])).
% 1.38/0.52  fof(f28,plain,(
% 1.38/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.52    inference(ennf_transformation,[],[f19])).
% 1.38/0.52  fof(f19,axiom,(
% 1.38/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.38/0.52  fof(f192,plain,(
% 1.38/0.52    spl5_12 | ~spl5_10),
% 1.38/0.52    inference(avatar_split_clause,[],[f184,f176,f190])).
% 1.38/0.52  fof(f190,plain,(
% 1.38/0.52    spl5_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.38/0.52  fof(f176,plain,(
% 1.38/0.52    spl5_10 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.38/0.52  fof(f184,plain,(
% 1.38/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_10),
% 1.38/0.52    inference(resolution,[],[f177,f65])).
% 1.38/0.52  fof(f65,plain,(
% 1.38/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.38/0.52    inference(cnf_transformation,[],[f26])).
% 1.38/0.52  fof(f26,plain,(
% 1.38/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.38/0.52    inference(ennf_transformation,[],[f4])).
% 1.38/0.52  fof(f4,axiom,(
% 1.38/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.38/0.52  fof(f177,plain,(
% 1.38/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl5_10),
% 1.38/0.52    inference(avatar_component_clause,[],[f176])).
% 1.38/0.52  fof(f178,plain,(
% 1.38/0.52    spl5_10 | ~spl5_9),
% 1.38/0.52    inference(avatar_split_clause,[],[f173,f168,f176])).
% 1.38/0.52  fof(f168,plain,(
% 1.38/0.52    spl5_9 <=> v1_xboole_0(k1_xboole_0)),
% 1.38/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.38/0.52  fof(f173,plain,(
% 1.38/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl5_9),
% 1.38/0.52    inference(resolution,[],[f169,f66])).
% 1.38/0.52  fof(f66,plain,(
% 1.38/0.52    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.38/0.52    inference(cnf_transformation,[],[f27])).
% 1.38/0.52  fof(f27,plain,(
% 1.38/0.52    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.38/0.52    inference(ennf_transformation,[],[f15])).
% 1.38/0.52  fof(f15,axiom,(
% 1.38/0.52    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.38/0.52  fof(f169,plain,(
% 1.38/0.52    v1_xboole_0(k1_xboole_0) | ~spl5_9),
% 1.38/0.52    inference(avatar_component_clause,[],[f168])).
% 1.38/0.52  fof(f171,plain,(
% 1.38/0.52    spl5_9),
% 1.38/0.52    inference(avatar_split_clause,[],[f166,f168])).
% 1.38/0.52  fof(f166,plain,(
% 1.38/0.52    v1_xboole_0(k1_xboole_0)),
% 1.38/0.52    inference(resolution,[],[f164,f149])).
% 1.38/0.52  fof(f164,plain,(
% 1.38/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.38/0.52    inference(resolution,[],[f77,f62])).
% 1.38/0.52  fof(f62,plain,(
% 1.38/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f9])).
% 1.38/0.52  fof(f9,axiom,(
% 1.38/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.52  fof(f77,plain,(
% 1.38/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.38/0.52    inference(cnf_transformation,[],[f32])).
% 1.38/0.52  fof(f32,plain,(
% 1.38/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.38/0.52    inference(flattening,[],[f31])).
% 1.38/0.52  fof(f31,plain,(
% 1.38/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.38/0.52    inference(ennf_transformation,[],[f10])).
% 1.38/0.52  fof(f10,axiom,(
% 1.38/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.38/0.52  fof(f126,plain,(
% 1.38/0.52    spl5_5),
% 1.38/0.52    inference(avatar_split_clause,[],[f58,f124])).
% 1.38/0.52  fof(f58,plain,(
% 1.38/0.52    v1_relat_1(sK1)),
% 1.38/0.52    inference(cnf_transformation,[],[f41])).
% 1.38/0.52  fof(f41,plain,(
% 1.38/0.52    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.38/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f40])).
% 1.38/0.52  fof(f40,plain,(
% 1.38/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.38/0.52    introduced(choice_axiom,[])).
% 1.38/0.52  fof(f24,plain,(
% 1.38/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.38/0.52    inference(flattening,[],[f23])).
% 1.38/0.52  fof(f23,plain,(
% 1.38/0.52    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.38/0.52    inference(ennf_transformation,[],[f21])).
% 1.38/0.52  fof(f21,negated_conjecture,(
% 1.38/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.38/0.52    inference(negated_conjecture,[],[f20])).
% 1.38/0.52  fof(f20,conjecture,(
% 1.38/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.38/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.38/0.52  fof(f122,plain,(
% 1.38/0.52    spl5_1),
% 1.38/0.52    inference(avatar_split_clause,[],[f59,f108])).
% 1.38/0.52  fof(f59,plain,(
% 1.38/0.52    v1_funct_1(sK1)),
% 1.38/0.52    inference(cnf_transformation,[],[f41])).
% 1.38/0.52  fof(f120,plain,(
% 1.38/0.52    spl5_4),
% 1.38/0.52    inference(avatar_split_clause,[],[f60,f118])).
% 1.38/0.52  fof(f60,plain,(
% 1.38/0.52    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.38/0.52    inference(cnf_transformation,[],[f41])).
% 1.38/0.52  fof(f116,plain,(
% 1.38/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.38/0.52    inference(avatar_split_clause,[],[f61,f114,f111,f108])).
% 1.38/0.52  fof(f61,plain,(
% 1.38/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 1.38/0.52    inference(cnf_transformation,[],[f41])).
% 1.38/0.52  % SZS output end Proof for theBenchmark
% 1.38/0.52  % (17507)------------------------------
% 1.38/0.52  % (17507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.52  % (17507)Termination reason: Refutation
% 1.38/0.52  
% 1.38/0.52  % (17507)Memory used [KB]: 11257
% 1.38/0.52  % (17507)Time elapsed: 0.127 s
% 1.38/0.52  % (17507)------------------------------
% 1.38/0.52  % (17507)------------------------------
% 1.38/0.52  % (17501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.53  % (17487)Success in time 0.191 s
%------------------------------------------------------------------------------
