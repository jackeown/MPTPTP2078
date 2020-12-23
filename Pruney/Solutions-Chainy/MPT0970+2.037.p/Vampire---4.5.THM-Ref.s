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
% DateTime   : Thu Dec  3 13:00:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 274 expanded)
%              Number of leaves         :   30 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  442 ( 862 expanded)
%              Number of equality atoms :  106 ( 238 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f61,f66,f71,f82,f87,f93,f102,f121,f129,f137,f157,f163,f204,f251,f311,f338,f423,f440,f447,f450,f499,f524])).

fof(f524,plain,
    ( spl6_27
    | ~ spl6_29
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | spl6_27
    | ~ spl6_29
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f522,f310])).

fof(f310,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_29
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f522,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl6_27
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f515,f267])).

fof(f267,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_27
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f515,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_33 ),
    inference(resolution,[],[f337,f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f337,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl6_33
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f499,plain,
    ( ~ spl6_27
    | spl6_12
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f498,f201,f118,f266])).

fof(f118,plain,
    ( spl6_12
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f201,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f498,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_12
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f120,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f120,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f450,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f448,f70])).

fof(f70,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f448,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_3
    | ~ spl6_42 ),
    inference(resolution,[],[f436,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f436,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | sK1 = k2_relset_1(X1,sK1,sK2) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl6_42
  <=> ! [X1] :
        ( sK1 = k2_relset_1(X1,sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f447,plain,
    ( ~ spl6_3
    | spl6_39
    | ~ spl6_43 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl6_3
    | spl6_39
    | ~ spl6_43 ),
    inference(resolution,[],[f445,f65])).

fof(f445,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl6_39
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f424,f439])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK1 != k2_relset_1(X0,sK1,sK2) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl6_43
  <=> ! [X0] :
        ( sK1 != k2_relset_1(X0,sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f424,plain,
    ( ! [X0] :
        ( sK1 = k2_relset_1(X0,sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl6_39 ),
    inference(resolution,[],[f422,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X1,X2),X1)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f422,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl6_39
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f440,plain,
    ( spl6_42
    | spl6_43
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f409,f68,f63,f438,f435])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( sK1 != k2_relset_1(X0,sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK1 = k2_relset_1(X1,sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) )
    | ~ spl6_3
    | spl6_4 ),
    inference(resolution,[],[f387,f37])).

fof(f387,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK1,sK2),X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_3
    | spl6_4 ),
    inference(resolution,[],[f180,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X2,X3),X3),X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f72,f70])).

fof(f72,plain,
    ( ! [X0] :
        ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f423,plain,
    ( ~ spl6_39
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f408,f148,f132,f68,f63,f50,f420])).

fof(f50,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f132,plain,
    ( spl6_14
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f148,plain,
    ( spl6_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f408,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(resolution,[],[f192,f180])).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0),X0),sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f191,f20])).

fof(f20,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f191,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0),X0),sK2)
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(superposition,[],[f189,f21])).

fof(f21,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f189,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f158,f149])).

fof(f149,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f158,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) )
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f56,f134])).

fof(f134,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f56,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f338,plain,
    ( spl6_33
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f283,f201,f160,f335])).

fof(f160,plain,
    ( spl6_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f283,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(superposition,[],[f162,f203])).

fof(f162,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f311,plain,
    ( spl6_29
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f281,f201,f126,f308])).

fof(f126,plain,
    ( spl6_13
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f281,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(superposition,[],[f128,f203])).

fof(f128,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f251,plain,
    ( spl6_7
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl6_7
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f249,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f249,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl6_7
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f226,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f226,plain,
    ( k2_relat_1(k1_xboole_0) != sK1
    | spl6_7
    | ~ spl6_20 ),
    inference(superposition,[],[f92,f199])).

fof(f199,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f92,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_7
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f204,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f171,f160,f126,f201,f197])).

fof(f171,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f165,f128])).

fof(f165,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(resolution,[],[f162,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f139,f99,f63,f160])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(superposition,[],[f65,f101])).

fof(f157,plain,
    ( ~ spl6_3
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl6_3
    | spl6_15 ),
    inference(resolution,[],[f155,f65])).

fof(f155,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_15 ),
    inference(resolution,[],[f150,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f150,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f137,plain,
    ( spl6_14
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f135,f95,f84,f132])).

fof(f84,plain,
    ( spl6_6
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f95,plain,
    ( spl6_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f135,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f97,f86])).

fof(f86,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f97,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f129,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f115,f99,f58,f126])).

fof(f58,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f115,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(superposition,[],[f60,f101])).

fof(f60,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f121,plain,
    ( ~ spl6_12
    | spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f116,f99,f95,f118])).

fof(f116,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f96,f101])).

fof(f96,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f102,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f77,f63,f58,f99,f95])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f74,f60])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,
    ( ~ spl6_7
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f88,f79,f68,f90])).

fof(f79,plain,
    ( spl6_5
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f88,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl6_4
    | ~ spl6_5 ),
    inference(superposition,[],[f70,f81])).

fof(f81,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f87,plain,
    ( spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f76,f63,f84])).

fof(f76,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f65,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f75,f63,f79])).

fof(f75,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f71,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (29803)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.43  % (29803)Refutation not found, incomplete strategy% (29803)------------------------------
% 0.21/0.43  % (29803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (29803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (29803)Memory used [KB]: 10618
% 0.21/0.43  % (29803)Time elapsed: 0.006 s
% 0.21/0.43  % (29803)------------------------------
% 0.21/0.43  % (29803)------------------------------
% 0.21/0.46  % (29795)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (29796)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (29798)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (29795)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f527,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f61,f66,f71,f82,f87,f93,f102,f121,f129,f137,f157,f163,f204,f251,f311,f338,f423,f440,f447,f450,f499,f524])).
% 0.21/0.47  fof(f524,plain,(
% 0.21/0.47    spl6_27 | ~spl6_29 | ~spl6_33),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f523])).
% 0.21/0.47  fof(f523,plain,(
% 0.21/0.47    $false | (spl6_27 | ~spl6_29 | ~spl6_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f522,f310])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f308])).
% 0.21/0.47  fof(f308,plain,(
% 0.21/0.47    spl6_29 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.47  fof(f522,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (spl6_27 | ~spl6_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f515,f267])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | spl6_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f266])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    spl6_27 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.47  fof(f515,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_33),
% 0.21/0.47    inference(resolution,[],[f337,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f337,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f335])).
% 0.21/0.47  fof(f335,plain,(
% 0.21/0.47    spl6_33 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.47  fof(f499,plain,(
% 0.21/0.47    ~spl6_27 | spl6_12 | ~spl6_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f498,f201,f118,f266])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl6_12 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    spl6_21 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.47  fof(f498,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl6_12 | ~spl6_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f120,f203])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl6_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f201])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | spl6_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f450,plain,(
% 0.21/0.47    ~spl6_3 | spl6_4 | ~spl6_42),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f449])).
% 0.21/0.47  fof(f449,plain,(
% 0.21/0.47    $false | (~spl6_3 | spl6_4 | ~spl6_42)),
% 0.21/0.47    inference(subsumption_resolution,[],[f448,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sK1 != k2_relset_1(sK0,sK1,sK2) | spl6_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl6_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.47  fof(f448,plain,(
% 0.21/0.47    sK1 = k2_relset_1(sK0,sK1,sK2) | (~spl6_3 | ~spl6_42)),
% 0.21/0.47    inference(resolution,[],[f436,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f436,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | sK1 = k2_relset_1(X1,sK1,sK2)) ) | ~spl6_42),
% 0.21/0.47    inference(avatar_component_clause,[],[f435])).
% 0.21/0.47  fof(f435,plain,(
% 0.21/0.47    spl6_42 <=> ! [X1] : (sK1 = k2_relset_1(X1,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.47  fof(f447,plain,(
% 0.21/0.47    ~spl6_3 | spl6_39 | ~spl6_43),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f446])).
% 0.21/0.47  fof(f446,plain,(
% 0.21/0.47    $false | (~spl6_3 | spl6_39 | ~spl6_43)),
% 0.21/0.47    inference(resolution,[],[f445,f65])).
% 0.21/0.47  fof(f445,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl6_39 | ~spl6_43)),
% 0.21/0.47    inference(subsumption_resolution,[],[f424,f439])).
% 0.21/0.47  fof(f439,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK1 != k2_relset_1(X0,sK1,sK2)) ) | ~spl6_43),
% 0.21/0.47    inference(avatar_component_clause,[],[f438])).
% 0.21/0.47  fof(f438,plain,(
% 0.21/0.47    spl6_43 <=> ! [X0] : (sK1 != k2_relset_1(X0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.47  fof(f424,plain,(
% 0.21/0.47    ( ! [X0] : (sK1 = k2_relset_1(X0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl6_39),
% 0.21/0.47    inference(resolution,[],[f422,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK4(X1,X2),X1) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.47  fof(f422,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK1,sK2),sK1) | spl6_39),
% 0.21/0.47    inference(avatar_component_clause,[],[f420])).
% 0.21/0.47  fof(f420,plain,(
% 0.21/0.47    spl6_39 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.47  fof(f440,plain,(
% 0.21/0.47    spl6_42 | spl6_43 | ~spl6_3 | spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f409,f68,f63,f438,f435])).
% 0.21/0.47  fof(f409,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sK1 != k2_relset_1(X0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK1 = k2_relset_1(X1,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) ) | (~spl6_3 | spl6_4)),
% 0.21/0.47    inference(resolution,[],[f387,f37])).
% 0.21/0.47  fof(f387,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK4(sK1,sK2),X1) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl6_3 | spl6_4)),
% 0.21/0.47    inference(resolution,[],[f180,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK5(X2,X3),X3),X2) | k2_relset_1(X0,X1,X2) != X1 | ~r2_hidden(X3,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)) ) | (~spl6_3 | spl6_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f72,f70])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f65,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f423,plain,(
% 0.21/0.47    ~spl6_39 | ~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_14 | ~spl6_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f408,f148,f132,f68,f63,f50,f420])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl6_14 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl6_15 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.47  fof(f408,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK1,sK2),sK1) | (~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_14 | ~spl6_15)),
% 0.21/0.47    inference(resolution,[],[f192,f180])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0),X0),sK2) | ~r2_hidden(X0,sK1)) ) | (~spl6_1 | ~spl6_14 | ~spl6_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f191,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0),X0),sK2) | ~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1)) ) | (~spl6_1 | ~spl6_14 | ~spl6_15)),
% 0.21/0.47    inference(superposition,[],[f189,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    ( ! [X4] : (r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) | ~r2_hidden(X4,sK0)) ) | (~spl6_1 | ~spl6_14 | ~spl6_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f158,f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl6_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f148])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X4] : (~r2_hidden(X4,sK0) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)) ) | (~spl6_1 | ~spl6_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f56,f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK2) | ~spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X4] : (~v1_relat_1(sK2) | ~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)) ) | ~spl6_1),
% 0.21/0.47    inference(resolution,[],[f52,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f338,plain,(
% 0.21/0.47    spl6_33 | ~spl6_17 | ~spl6_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f283,f201,f160,f335])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl6_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_17 | ~spl6_21)),
% 0.21/0.47    inference(superposition,[],[f162,f203])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f160])).
% 0.21/0.47  fof(f311,plain,(
% 0.21/0.47    spl6_29 | ~spl6_13 | ~spl6_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f281,f201,f126,f308])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl6_13 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_13 | ~spl6_21)),
% 0.21/0.47    inference(superposition,[],[f128,f203])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f126])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    spl6_7 | ~spl6_9 | ~spl6_20),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.47  fof(f250,plain,(
% 0.21/0.47    $false | (spl6_7 | ~spl6_9 | ~spl6_20)),
% 0.21/0.47    inference(subsumption_resolution,[],[f249,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f249,plain,(
% 0.21/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl6_7 | ~spl6_9 | ~spl6_20)),
% 0.21/0.47    inference(forward_demodulation,[],[f226,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl6_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl6_9 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    k2_relat_1(k1_xboole_0) != sK1 | (spl6_7 | ~spl6_20)),
% 0.21/0.47    inference(superposition,[],[f92,f199])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | ~spl6_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f197])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    spl6_20 <=> k1_xboole_0 = sK2),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2) | spl6_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl6_7 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    spl6_20 | spl6_21 | ~spl6_13 | ~spl6_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f171,f160,f126,f201,f197])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl6_13 | ~spl6_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f165,f128])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_17),
% 0.21/0.47    inference(resolution,[],[f162,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl6_17 | ~spl6_3 | ~spl6_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f139,f99,f63,f160])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_9)),
% 0.21/0.47    inference(superposition,[],[f65,f101])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~spl6_3 | spl6_15),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    $false | (~spl6_3 | spl6_15)),
% 0.21/0.47    inference(resolution,[],[f155,f65])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_15),
% 0.21/0.47    inference(resolution,[],[f150,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl6_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f148])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl6_14 | ~spl6_6 | ~spl6_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f135,f95,f84,f132])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl6_6 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl6_8 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK2) | (~spl6_6 | ~spl6_8)),
% 0.21/0.47    inference(superposition,[],[f97,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl6_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl6_13 | ~spl6_2 | ~spl6_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f99,f58,f126])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl6_2 | ~spl6_9)),
% 0.21/0.47    inference(superposition,[],[f60,f101])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,sK1) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~spl6_12 | spl6_8 | ~spl6_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f99,f95,f118])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl6_8 | ~spl6_9)),
% 0.21/0.47    inference(forward_demodulation,[],[f96,f101])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    sK0 != k1_relset_1(sK0,sK1,sK2) | spl6_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl6_8 | spl6_9 | ~spl6_2 | ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f77,f63,f58,f99,f95])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_2 | ~spl6_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f60])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f65,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~spl6_7 | spl6_4 | ~spl6_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f79,f68,f90])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl6_5 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    sK1 != k2_relat_1(sK2) | (spl6_4 | ~spl6_5)),
% 0.21/0.47    inference(superposition,[],[f70,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl6_6 | ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f76,f63,f84])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f65,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl6_5 | ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f63,f79])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f65,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f68])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f63])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29795)------------------------------
% 0.21/0.47  % (29795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29795)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29795)Memory used [KB]: 10874
% 0.21/0.47  % (29795)Time elapsed: 0.063 s
% 0.21/0.47  % (29795)------------------------------
% 0.21/0.47  % (29795)------------------------------
% 0.21/0.47  % (29789)Success in time 0.113 s
%------------------------------------------------------------------------------
