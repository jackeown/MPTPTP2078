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
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 281 expanded)
%              Number of leaves         :   39 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  483 (1035 expanded)
%              Number of equality atoms :  102 ( 194 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f124,f147,f167,f172,f180,f188,f208,f215,f296,f322,f326,f358,f425,f433,f474,f589,f593,f633,f649,f650])).

fof(f650,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f649,plain,
    ( ~ spl10_11
    | ~ spl10_2
    | spl10_43
    | ~ spl10_29
    | ~ spl10_41
    | spl10_44 ),
    inference(avatar_split_clause,[],[f638,f630,f591,f355,f626,f83,f144])).

fof(f144,plain,
    ( spl10_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f83,plain,
    ( spl10_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f626,plain,
    ( spl10_43
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f355,plain,
    ( spl10_29
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f591,plain,
    ( spl10_41
  <=> ! [X2] :
        ( r2_hidden(sK4(sK3,X2),sK0)
        | sK3 = X2
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f630,plain,
    ( spl10_44
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f638,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_29
    | ~ spl10_41
    | spl10_44 ),
    inference(trivial_inequality_removal,[],[f637])).

fof(f637,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_29
    | ~ spl10_41
    | spl10_44 ),
    inference(forward_demodulation,[],[f634,f357])).

fof(f357,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f355])).

fof(f634,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_41
    | spl10_44 ),
    inference(resolution,[],[f632,f592])).

fof(f592,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK3,X2),sK0)
        | sK3 = X2
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f591])).

fof(f632,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl10_44 ),
    inference(avatar_component_clause,[],[f630])).

fof(f633,plain,
    ( ~ spl10_11
    | ~ spl10_2
    | spl10_43
    | ~ spl10_44
    | ~ spl10_29
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f624,f587,f355,f630,f626,f83,f144])).

fof(f587,plain,
    ( spl10_40
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f624,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_29
    | ~ spl10_40 ),
    inference(trivial_inequality_removal,[],[f623])).

fof(f623,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_29
    | ~ spl10_40 ),
    inference(forward_demodulation,[],[f611,f357])).

fof(f611,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | ~ spl10_40 ),
    inference(equality_resolution,[],[f588])).

fof(f588,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f587])).

fof(f593,plain,
    ( ~ spl10_8
    | ~ spl10_1
    | spl10_41
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f258,f212,f591,f78,f121])).

fof(f121,plain,
    ( spl10_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f78,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f212,plain,
    ( spl10_22
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f258,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK3,X2),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X2 )
    | ~ spl10_22 ),
    inference(superposition,[],[f41,f214])).

fof(f214,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f589,plain,
    ( ~ spl10_8
    | spl10_40
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f530,f212,f587,f121])).

fof(f530,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | sK3 = X0
        | ~ r2_hidden(sK4(sK3,X0),sK0) )
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f165,f214])).

fof(f165,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(global_subsumption,[],[f33,f163])).

fof(f163,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(superposition,[],[f42,f32])).

fof(f32,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f474,plain,
    ( ~ spl10_34
    | spl10_5
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f473,f186,f177,f98,f430])).

fof(f430,plain,
    ( spl10_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f98,plain,
    ( spl10_5
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f177,plain,
    ( spl10_16
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f186,plain,
    ( spl10_18
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f473,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_5
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(resolution,[],[f445,f179])).

fof(f179,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X0)
        | ~ v1_xboole_0(X0) )
    | spl10_5
    | ~ spl10_18 ),
    inference(superposition,[],[f100,f438])).

fof(f438,plain,
    ( ! [X0] :
        ( sK3 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f386,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f386,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(X0,sK3),X0)
        | sK3 = X0 )
    | ~ spl10_18 ),
    inference(resolution,[],[f187,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f187,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f100,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f433,plain,
    ( spl10_34
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f426,f423,f430])).

fof(f423,plain,
    ( spl10_33
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f426,plain,
    ( v1_xboole_0(sK2)
    | ~ spl10_33 ),
    inference(resolution,[],[f424,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f424,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f423])).

fof(f425,plain,
    ( ~ spl10_17
    | spl10_33
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f189,f108,f423,f182])).

fof(f182,plain,
    ( spl10_17
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f108,plain,
    ( spl10_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_7 ),
    inference(resolution,[],[f142,f44])).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f358,plain,
    ( ~ spl10_7
    | spl10_29
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f346,f293,f355,f108])).

fof(f293,plain,
    ( spl10_27
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f346,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_27 ),
    inference(superposition,[],[f295,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f295,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f293])).

fof(f326,plain,(
    spl10_28 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl10_28 ),
    inference(unit_resulting_resolution,[],[f40,f321])).

fof(f321,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl10_28
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f322,plain,
    ( ~ spl10_28
    | spl10_17
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f316,f205,f182,f319])).

fof(f205,plain,
    ( spl10_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f316,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_17
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f309,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f309,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl10_17
    | ~ spl10_21 ),
    inference(backward_demodulation,[],[f184,f207])).

fof(f207,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f184,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f296,plain,
    ( ~ spl10_4
    | spl10_27
    | spl10_21
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f139,f108,f205,f293,f93])).

fof(f93,plain,
    ( spl10_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f215,plain,
    ( ~ spl10_6
    | spl10_22
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f209,f201,f212,f103])).

fof(f103,plain,
    ( spl10_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f201,plain,
    ( spl10_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f209,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_20 ),
    inference(superposition,[],[f203,f58])).

fof(f203,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f208,plain,
    ( ~ spl10_3
    | spl10_20
    | spl10_21
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f116,f103,f205,f201,f88])).

fof(f88,plain,
    ( spl10_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f105,f66])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f188,plain,
    ( ~ spl10_17
    | spl10_18
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f173,f103,f186,f182])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f119,f44])).

fof(f119,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl10_6 ),
    inference(resolution,[],[f105,f48])).

fof(f180,plain,
    ( spl10_12
    | spl10_16
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f140,f108,f177,f149])).

fof(f149,plain,
    ( spl10_12
  <=> sP9(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f140,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP9(sK1,sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP9(X1,X0) ) ),
    inference(cnf_transformation,[],[f75_D])).

fof(f75_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP9(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f172,plain,
    ( spl10_12
    | spl10_15
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f117,f103,f169,f149])).

fof(f169,plain,
    ( spl10_15
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f117,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | sP9(sK1,sK0)
    | ~ spl10_6 ),
    inference(resolution,[],[f105,f75])).

fof(f167,plain,
    ( ~ spl10_12
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f141,f108,f149])).

fof(f141,plain,
    ( ~ sP9(sK1,sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP9(X1,X0) ) ),
    inference(general_splitting,[],[f67,f75_D])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f147,plain,
    ( spl10_11
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f135,f108,f144])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( spl10_8
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f112,f103,f121])).

fof(f112,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f105,f57])).

fof(f111,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f39,f108])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f35,f103])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f33,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.20/0.51  % (3068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.51  % (3066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.52  % (3073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.52  % (3065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.52  % (3064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (3071)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.53  % (3085)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (3063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (3082)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.54  % (3089)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (3078)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (3091)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (3076)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (3090)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (3088)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (3079)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (3072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.54  % (3083)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.54  % (3087)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.54  % (3072)Refutation not found, incomplete strategy% (3072)------------------------------
% 1.31/0.54  % (3072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (3072)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (3072)Memory used [KB]: 10746
% 1.31/0.54  % (3072)Time elapsed: 0.142 s
% 1.31/0.54  % (3072)------------------------------
% 1.31/0.54  % (3072)------------------------------
% 1.31/0.54  % (3084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.55  % (3069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.55  % (3070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.55  % (3080)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % (3081)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.56  % (3074)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.56  % (3062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.57  % (3067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.57  % (3086)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.57  % (3084)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  fof(f651,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f124,f147,f167,f172,f180,f188,f208,f215,f296,f322,f326,f358,f425,f433,f474,f589,f593,f633,f649,f650])).
% 1.31/0.57  fof(f650,plain,(
% 1.31/0.57    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.31/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.31/0.57  fof(f649,plain,(
% 1.31/0.57    ~spl10_11 | ~spl10_2 | spl10_43 | ~spl10_29 | ~spl10_41 | spl10_44),
% 1.31/0.57    inference(avatar_split_clause,[],[f638,f630,f591,f355,f626,f83,f144])).
% 1.31/0.57  fof(f144,plain,(
% 1.31/0.57    spl10_11 <=> v1_relat_1(sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.31/0.57  fof(f83,plain,(
% 1.31/0.57    spl10_2 <=> v1_funct_1(sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.31/0.57  fof(f626,plain,(
% 1.31/0.57    spl10_43 <=> sK2 = sK3),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 1.31/0.57  fof(f355,plain,(
% 1.31/0.57    spl10_29 <=> sK0 = k1_relat_1(sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 1.31/0.57  fof(f591,plain,(
% 1.31/0.57    spl10_41 <=> ! [X2] : (r2_hidden(sK4(sK3,X2),sK0) | sK3 = X2 | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 1.31/0.57  fof(f630,plain,(
% 1.31/0.57    spl10_44 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 1.31/0.57  fof(f638,plain,(
% 1.31/0.57    sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl10_29 | ~spl10_41 | spl10_44)),
% 1.31/0.57    inference(trivial_inequality_removal,[],[f637])).
% 1.31/0.57  fof(f637,plain,(
% 1.31/0.57    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl10_29 | ~spl10_41 | spl10_44)),
% 1.31/0.57    inference(forward_demodulation,[],[f634,f357])).
% 1.31/0.57  fof(f357,plain,(
% 1.31/0.57    sK0 = k1_relat_1(sK2) | ~spl10_29),
% 1.31/0.57    inference(avatar_component_clause,[],[f355])).
% 1.31/0.57  fof(f634,plain,(
% 1.31/0.57    sK2 = sK3 | sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl10_41 | spl10_44)),
% 1.31/0.57    inference(resolution,[],[f632,f592])).
% 1.31/0.57  fof(f592,plain,(
% 1.31/0.57    ( ! [X2] : (r2_hidden(sK4(sK3,X2),sK0) | sK3 = X2 | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl10_41),
% 1.31/0.57    inference(avatar_component_clause,[],[f591])).
% 1.31/0.57  fof(f632,plain,(
% 1.31/0.57    ~r2_hidden(sK4(sK3,sK2),sK0) | spl10_44),
% 1.31/0.57    inference(avatar_component_clause,[],[f630])).
% 1.31/0.57  fof(f633,plain,(
% 1.31/0.57    ~spl10_11 | ~spl10_2 | spl10_43 | ~spl10_44 | ~spl10_29 | ~spl10_40),
% 1.31/0.57    inference(avatar_split_clause,[],[f624,f587,f355,f630,f626,f83,f144])).
% 1.31/0.57  fof(f587,plain,(
% 1.31/0.57    spl10_40 <=> ! [X0] : (k1_relat_1(X0) != sK0 | ~r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 1.31/0.57  fof(f624,plain,(
% 1.31/0.57    ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl10_29 | ~spl10_40)),
% 1.31/0.57    inference(trivial_inequality_removal,[],[f623])).
% 1.31/0.57  fof(f623,plain,(
% 1.31/0.57    sK0 != sK0 | ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl10_29 | ~spl10_40)),
% 1.31/0.57    inference(forward_demodulation,[],[f611,f357])).
% 1.31/0.57  fof(f611,plain,(
% 1.31/0.57    ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | ~spl10_40),
% 1.31/0.57    inference(equality_resolution,[],[f588])).
% 1.31/0.57  fof(f588,plain,(
% 1.31/0.57    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl10_40),
% 1.31/0.57    inference(avatar_component_clause,[],[f587])).
% 1.31/0.57  fof(f593,plain,(
% 1.31/0.57    ~spl10_8 | ~spl10_1 | spl10_41 | ~spl10_22),
% 1.31/0.57    inference(avatar_split_clause,[],[f258,f212,f591,f78,f121])).
% 1.31/0.57  fof(f121,plain,(
% 1.31/0.57    spl10_8 <=> v1_relat_1(sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.31/0.57  fof(f78,plain,(
% 1.31/0.57    spl10_1 <=> v1_funct_1(sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.31/0.57  fof(f212,plain,(
% 1.31/0.57    spl10_22 <=> sK0 = k1_relat_1(sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.31/0.57  fof(f258,plain,(
% 1.31/0.57    ( ! [X2] : (r2_hidden(sK4(sK3,X2),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | ~v1_relat_1(sK3) | sK3 = X2) ) | ~spl10_22),
% 1.31/0.57    inference(superposition,[],[f41,f214])).
% 1.31/0.57  fof(f214,plain,(
% 1.31/0.57    sK0 = k1_relat_1(sK3) | ~spl10_22),
% 1.31/0.57    inference(avatar_component_clause,[],[f212])).
% 1.31/0.57  fof(f41,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f20])).
% 1.31/0.57  fof(f20,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.57    inference(flattening,[],[f19])).
% 1.31/0.57  fof(f19,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f9])).
% 1.31/0.57  fof(f9,axiom,(
% 1.31/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.31/0.57  fof(f589,plain,(
% 1.31/0.57    ~spl10_8 | spl10_40 | ~spl10_22),
% 1.31/0.57    inference(avatar_split_clause,[],[f530,f212,f587,f121])).
% 1.31/0.57  fof(f530,plain,(
% 1.31/0.57    ( ! [X0] : (k1_relat_1(X0) != sK0 | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) ) | ~spl10_22),
% 1.31/0.57    inference(forward_demodulation,[],[f165,f214])).
% 1.31/0.57  fof(f165,plain,(
% 1.31/0.57    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 1.31/0.57    inference(global_subsumption,[],[f33,f163])).
% 1.31/0.57  fof(f163,plain,(
% 1.31/0.57    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 1.31/0.57    inference(superposition,[],[f42,f32])).
% 1.31/0.57  fof(f32,plain,(
% 1.31/0.57    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f18,plain,(
% 1.31/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.31/0.57    inference(flattening,[],[f17])).
% 1.31/0.57  fof(f17,plain,(
% 1.31/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.31/0.57    inference(ennf_transformation,[],[f16])).
% 1.31/0.57  fof(f16,negated_conjecture,(
% 1.31/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.31/0.57    inference(negated_conjecture,[],[f15])).
% 1.31/0.57  fof(f15,conjecture,(
% 1.31/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.31/0.57  fof(f42,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f20])).
% 1.31/0.57  fof(f33,plain,(
% 1.31/0.57    v1_funct_1(sK3)),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f474,plain,(
% 1.31/0.57    ~spl10_34 | spl10_5 | ~spl10_16 | ~spl10_18),
% 1.31/0.57    inference(avatar_split_clause,[],[f473,f186,f177,f98,f430])).
% 1.31/0.57  fof(f430,plain,(
% 1.31/0.57    spl10_34 <=> v1_xboole_0(sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 1.31/0.57  fof(f98,plain,(
% 1.31/0.57    spl10_5 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.31/0.57  fof(f177,plain,(
% 1.31/0.57    spl10_16 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.31/0.57  fof(f186,plain,(
% 1.31/0.57    spl10_18 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.31/0.57  fof(f473,plain,(
% 1.31/0.57    ~v1_xboole_0(sK2) | (spl10_5 | ~spl10_16 | ~spl10_18)),
% 1.31/0.57    inference(resolution,[],[f445,f179])).
% 1.31/0.57  fof(f179,plain,(
% 1.31/0.57    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_16),
% 1.31/0.57    inference(avatar_component_clause,[],[f177])).
% 1.31/0.57  fof(f445,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK1,sK2,X0) | ~v1_xboole_0(X0)) ) | (spl10_5 | ~spl10_18)),
% 1.31/0.57    inference(superposition,[],[f100,f438])).
% 1.31/0.57  fof(f438,plain,(
% 1.31/0.57    ( ! [X0] : (sK3 = X0 | ~v1_xboole_0(X0)) ) | ~spl10_18),
% 1.31/0.57    inference(resolution,[],[f386,f44])).
% 1.31/0.57  fof(f44,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f1])).
% 1.31/0.57  fof(f1,axiom,(
% 1.31/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.31/0.57  fof(f386,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(sK7(X0,sK3),X0) | sK3 = X0) ) | ~spl10_18),
% 1.31/0.57    inference(resolution,[],[f187,f49])).
% 1.31/0.57  fof(f49,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0) | X0 = X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f23])).
% 1.31/0.57  fof(f23,plain,(
% 1.31/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.31/0.57    inference(ennf_transformation,[],[f4])).
% 1.31/0.57  fof(f4,axiom,(
% 1.31/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.31/0.57  fof(f187,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl10_18),
% 1.31/0.57    inference(avatar_component_clause,[],[f186])).
% 1.31/0.57  fof(f100,plain,(
% 1.31/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl10_5),
% 1.31/0.57    inference(avatar_component_clause,[],[f98])).
% 1.31/0.57  fof(f433,plain,(
% 1.31/0.57    spl10_34 | ~spl10_33),
% 1.31/0.57    inference(avatar_split_clause,[],[f426,f423,f430])).
% 1.31/0.57  fof(f423,plain,(
% 1.31/0.57    spl10_33 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 1.31/0.57  fof(f426,plain,(
% 1.31/0.57    v1_xboole_0(sK2) | ~spl10_33),
% 1.31/0.57    inference(resolution,[],[f424,f43])).
% 1.31/0.57  fof(f43,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f1])).
% 1.31/0.57  fof(f424,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl10_33),
% 1.31/0.57    inference(avatar_component_clause,[],[f423])).
% 1.31/0.57  fof(f425,plain,(
% 1.31/0.57    ~spl10_17 | spl10_33 | ~spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f189,f108,f423,f182])).
% 1.31/0.57  fof(f182,plain,(
% 1.31/0.57    spl10_17 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.31/0.57  fof(f108,plain,(
% 1.31/0.57    spl10_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.31/0.57  fof(f189,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) ) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f142,f44])).
% 1.31/0.57  fof(f142,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f110,f48])).
% 1.31/0.57  fof(f48,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  fof(f22,plain,(
% 1.31/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f7])).
% 1.31/0.57  fof(f7,axiom,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.31/0.57  fof(f110,plain,(
% 1.31/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_7),
% 1.31/0.57    inference(avatar_component_clause,[],[f108])).
% 1.31/0.57  fof(f358,plain,(
% 1.31/0.57    ~spl10_7 | spl10_29 | ~spl10_27),
% 1.31/0.57    inference(avatar_split_clause,[],[f346,f293,f355,f108])).
% 1.31/0.57  fof(f293,plain,(
% 1.31/0.57    spl10_27 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 1.31/0.57  fof(f346,plain,(
% 1.31/0.57    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_27),
% 1.31/0.57    inference(superposition,[],[f295,f58])).
% 1.31/0.57  fof(f58,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f26])).
% 1.31/0.57  fof(f26,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.57    inference(ennf_transformation,[],[f12])).
% 1.31/0.57  fof(f12,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.31/0.57  fof(f295,plain,(
% 1.31/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl10_27),
% 1.31/0.57    inference(avatar_component_clause,[],[f293])).
% 1.31/0.57  fof(f326,plain,(
% 1.31/0.57    spl10_28),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f323])).
% 1.31/0.57  fof(f323,plain,(
% 1.31/0.57    $false | spl10_28),
% 1.31/0.57    inference(unit_resulting_resolution,[],[f40,f321])).
% 1.31/0.57  fof(f321,plain,(
% 1.31/0.57    ~v1_xboole_0(k1_xboole_0) | spl10_28),
% 1.31/0.57    inference(avatar_component_clause,[],[f319])).
% 1.31/0.57  fof(f319,plain,(
% 1.31/0.57    spl10_28 <=> v1_xboole_0(k1_xboole_0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 1.31/0.57  fof(f40,plain,(
% 1.31/0.57    v1_xboole_0(k1_xboole_0)),
% 1.31/0.57    inference(cnf_transformation,[],[f3])).
% 1.31/0.57  fof(f3,axiom,(
% 1.31/0.57    v1_xboole_0(k1_xboole_0)),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.31/0.57  fof(f322,plain,(
% 1.31/0.57    ~spl10_28 | spl10_17 | ~spl10_21),
% 1.31/0.57    inference(avatar_split_clause,[],[f316,f205,f182,f319])).
% 1.31/0.57  fof(f205,plain,(
% 1.31/0.57    spl10_21 <=> k1_xboole_0 = sK1),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.31/0.57  fof(f316,plain,(
% 1.31/0.57    ~v1_xboole_0(k1_xboole_0) | (spl10_17 | ~spl10_21)),
% 1.31/0.57    inference(forward_demodulation,[],[f309,f68])).
% 1.31/0.57  fof(f68,plain,(
% 1.31/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.31/0.57    inference(equality_resolution,[],[f56])).
% 1.31/0.57  fof(f56,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f5])).
% 1.31/0.57  fof(f5,axiom,(
% 1.31/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.31/0.57  fof(f309,plain,(
% 1.31/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl10_17 | ~spl10_21)),
% 1.31/0.57    inference(backward_demodulation,[],[f184,f207])).
% 1.31/0.57  fof(f207,plain,(
% 1.31/0.57    k1_xboole_0 = sK1 | ~spl10_21),
% 1.31/0.57    inference(avatar_component_clause,[],[f205])).
% 1.31/0.57  fof(f184,plain,(
% 1.31/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl10_17),
% 1.31/0.57    inference(avatar_component_clause,[],[f182])).
% 1.31/0.57  fof(f296,plain,(
% 1.31/0.57    ~spl10_4 | spl10_27 | spl10_21 | ~spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f139,f108,f205,f293,f93])).
% 1.31/0.57  fof(f93,plain,(
% 1.31/0.57    spl10_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.31/0.57  fof(f139,plain,(
% 1.31/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f110,f66])).
% 1.31/0.57  fof(f66,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f29])).
% 1.31/0.57  fof(f29,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.57    inference(flattening,[],[f28])).
% 1.31/0.57  fof(f28,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.57    inference(ennf_transformation,[],[f14])).
% 1.31/0.57  fof(f14,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.31/0.57  fof(f215,plain,(
% 1.31/0.57    ~spl10_6 | spl10_22 | ~spl10_20),
% 1.31/0.57    inference(avatar_split_clause,[],[f209,f201,f212,f103])).
% 1.31/0.57  fof(f103,plain,(
% 1.31/0.57    spl10_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.31/0.57  fof(f201,plain,(
% 1.31/0.57    spl10_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 1.31/0.57  fof(f209,plain,(
% 1.31/0.57    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_20),
% 1.31/0.57    inference(superposition,[],[f203,f58])).
% 1.31/0.57  fof(f203,plain,(
% 1.31/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl10_20),
% 1.31/0.57    inference(avatar_component_clause,[],[f201])).
% 1.31/0.57  fof(f208,plain,(
% 1.31/0.57    ~spl10_3 | spl10_20 | spl10_21 | ~spl10_6),
% 1.31/0.57    inference(avatar_split_clause,[],[f116,f103,f205,f201,f88])).
% 1.31/0.57  fof(f88,plain,(
% 1.31/0.57    spl10_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.31/0.57  fof(f116,plain,(
% 1.31/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl10_6),
% 1.31/0.57    inference(resolution,[],[f105,f66])).
% 1.31/0.57  fof(f105,plain,(
% 1.31/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_6),
% 1.31/0.57    inference(avatar_component_clause,[],[f103])).
% 1.31/0.57  fof(f188,plain,(
% 1.31/0.57    ~spl10_17 | spl10_18 | ~spl10_6),
% 1.31/0.57    inference(avatar_split_clause,[],[f173,f103,f186,f182])).
% 1.31/0.57  fof(f173,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) ) | ~spl10_6),
% 1.31/0.57    inference(resolution,[],[f119,f44])).
% 1.31/0.57  fof(f119,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) ) | ~spl10_6),
% 1.31/0.57    inference(resolution,[],[f105,f48])).
% 1.31/0.57  fof(f180,plain,(
% 1.31/0.57    spl10_12 | spl10_16 | ~spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f140,f108,f177,f149])).
% 1.31/0.57  fof(f149,plain,(
% 1.31/0.57    spl10_12 <=> sP9(sK1,sK0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.31/0.57  fof(f140,plain,(
% 1.31/0.57    r2_relset_1(sK0,sK1,sK2,sK2) | sP9(sK1,sK0) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f110,f75])).
% 1.31/0.57  fof(f75,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP9(X1,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f75_D])).
% 1.31/0.57  fof(f75_D,plain,(
% 1.31/0.57    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP9(X1,X0)) )),
% 1.31/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.31/0.57  fof(f172,plain,(
% 1.31/0.57    spl10_12 | spl10_15 | ~spl10_6),
% 1.31/0.57    inference(avatar_split_clause,[],[f117,f103,f169,f149])).
% 1.31/0.57  fof(f169,plain,(
% 1.31/0.57    spl10_15 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.31/0.57  fof(f117,plain,(
% 1.31/0.57    r2_relset_1(sK0,sK1,sK3,sK3) | sP9(sK1,sK0) | ~spl10_6),
% 1.31/0.57    inference(resolution,[],[f105,f75])).
% 1.31/0.57  fof(f167,plain,(
% 1.31/0.57    ~spl10_12 | ~spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f141,f108,f149])).
% 1.31/0.57  fof(f141,plain,(
% 1.31/0.57    ~sP9(sK1,sK0) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f110,f76])).
% 1.31/0.57  fof(f76,plain,(
% 1.31/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP9(X1,X0)) )),
% 1.31/0.57    inference(general_splitting,[],[f67,f75_D])).
% 1.31/0.57  fof(f67,plain,(
% 1.31/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f31])).
% 1.31/0.57  fof(f31,plain,(
% 1.31/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.57    inference(flattening,[],[f30])).
% 1.31/0.57  fof(f30,plain,(
% 1.31/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.31/0.57    inference(ennf_transformation,[],[f13])).
% 1.31/0.57  fof(f13,axiom,(
% 1.31/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.31/0.57  fof(f147,plain,(
% 1.31/0.57    spl10_11 | ~spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f135,f108,f144])).
% 1.31/0.57  fof(f135,plain,(
% 1.31/0.57    v1_relat_1(sK2) | ~spl10_7),
% 1.31/0.57    inference(resolution,[],[f110,f57])).
% 1.31/0.57  fof(f57,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f25])).
% 1.31/0.57  fof(f25,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.57    inference(ennf_transformation,[],[f10])).
% 1.31/0.57  fof(f10,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.57  fof(f124,plain,(
% 1.31/0.57    spl10_8 | ~spl10_6),
% 1.31/0.57    inference(avatar_split_clause,[],[f112,f103,f121])).
% 1.31/0.57  fof(f112,plain,(
% 1.31/0.57    v1_relat_1(sK3) | ~spl10_6),
% 1.31/0.57    inference(resolution,[],[f105,f57])).
% 1.31/0.57  fof(f111,plain,(
% 1.31/0.57    spl10_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f39,f108])).
% 1.31/0.57  fof(f39,plain,(
% 1.31/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f106,plain,(
% 1.31/0.57    spl10_6),
% 1.31/0.57    inference(avatar_split_clause,[],[f35,f103])).
% 1.31/0.57  fof(f35,plain,(
% 1.31/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f101,plain,(
% 1.31/0.57    ~spl10_5),
% 1.31/0.57    inference(avatar_split_clause,[],[f36,f98])).
% 1.31/0.57  fof(f36,plain,(
% 1.31/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f96,plain,(
% 1.31/0.57    spl10_4),
% 1.31/0.57    inference(avatar_split_clause,[],[f38,f93])).
% 1.31/0.57  fof(f38,plain,(
% 1.31/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f91,plain,(
% 1.31/0.57    spl10_3),
% 1.31/0.57    inference(avatar_split_clause,[],[f34,f88])).
% 1.31/0.57  fof(f34,plain,(
% 1.31/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f86,plain,(
% 1.31/0.57    spl10_2),
% 1.31/0.57    inference(avatar_split_clause,[],[f37,f83])).
% 1.31/0.57  fof(f37,plain,(
% 1.31/0.57    v1_funct_1(sK2)),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f81,plain,(
% 1.31/0.57    spl10_1),
% 1.31/0.57    inference(avatar_split_clause,[],[f33,f78])).
% 1.31/0.57  % SZS output end Proof for theBenchmark
% 1.31/0.57  % (3084)------------------------------
% 1.31/0.57  % (3084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (3084)Termination reason: Refutation
% 1.31/0.57  
% 1.31/0.57  % (3084)Memory used [KB]: 11129
% 1.31/0.57  % (3084)Time elapsed: 0.138 s
% 1.31/0.57  % (3084)------------------------------
% 1.31/0.57  % (3084)------------------------------
% 1.31/0.58  % (3061)Success in time 0.217 s
%------------------------------------------------------------------------------
