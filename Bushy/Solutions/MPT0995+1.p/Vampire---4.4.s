%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t43_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:45 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 145 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 ( 562 expanded)
%              Number of equality atoms :   57 ( 125 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f100,f104,f108,f130,f138,f150,f171,f175,f182,f188,f315,f332])).

fof(f332,plain,
    ( ~ spl10_0
    | ~ spl10_26
    | spl10_31
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_26
    | ~ spl10_31
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f330,f181])).

fof(f181,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_31
  <=> ~ r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f330,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_0
    | ~ spl10_26
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f329,f170])).

fof(f170,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl10_26
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f329,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_0
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f327,f95])).

fof(f95,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl10_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f327,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_64 ),
    inference(resolution,[],[f314,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',d12_funct_1)).

fof(f314,plain,
    ( sP7(sK4,sK2,sK3)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl10_64
  <=> sP7(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f315,plain,
    ( spl10_64
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f307,f186,f136,f102,f98,f313])).

fof(f98,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f102,plain,
    ( spl10_4
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f136,plain,
    ( spl10_16
  <=> k1_funct_1(sK3,sK5) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f186,plain,
    ( spl10_32
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f307,plain,
    ( sP7(sK4,sK2,sK3)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(resolution,[],[f288,f103])).

fof(f103,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(sK4,X0,sK3) )
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(forward_demodulation,[],[f287,f137])).

fof(f137,plain,
    ( k1_funct_1(sK3,sK5) = sK4
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(k1_funct_1(sK3,sK5),X0,sK3) )
    | ~ spl10_2
    | ~ spl10_32 ),
    inference(resolution,[],[f193,f99])).

fof(f99,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | sP7(k1_funct_1(sK3,X0),X1,sK3) )
    | ~ spl10_32 ),
    inference(superposition,[],[f87,f187])).

fof(f187,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f186])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | sP7(k1_funct_1(X0,X4),X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f188,plain,
    ( spl10_32
    | spl10_7
    | ~ spl10_12
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f166,f148,f128,f106,f186])).

fof(f106,plain,
    ( spl10_7
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f128,plain,
    ( spl10_12
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f148,plain,
    ( spl10_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f166,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl10_7
    | ~ spl10_12
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f159,f165])).

fof(f165,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl10_7
    | ~ spl10_12
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f164,f129])).

fof(f129,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f164,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_7
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f158,f107])).

fof(f107,plain,
    ( k1_xboole_0 != sK1
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_22 ),
    inference(resolution,[],[f149,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',d1_funct_2)).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f148])).

fof(f159,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_22 ),
    inference(resolution,[],[f149,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',redefinition_k1_relset_1)).

fof(f182,plain,
    ( ~ spl10_31
    | ~ spl10_22
    | spl10_29 ),
    inference(avatar_split_clause,[],[f176,f173,f148,f180])).

fof(f173,plain,
    ( spl10_29
  <=> ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f176,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_22
    | ~ spl10_29 ),
    inference(forward_demodulation,[],[f174,f155])).

fof(f155,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_22 ),
    inference(resolution,[],[f149,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',redefinition_k7_relset_1)).

fof(f174,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,(
    ~ spl10_29 ),
    inference(avatar_split_clause,[],[f52,f173])).

fof(f52,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',t43_funct_2)).

fof(f171,plain,
    ( spl10_26
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f160,f148,f169])).

fof(f160,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_22 ),
    inference(resolution,[],[f149,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t43_funct_2.p',cc1_relset_1)).

fof(f150,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f55,f148])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f51,f136])).

fof(f51,plain,(
    k1_funct_1(sK3,sK5) = sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f130,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f54,f128])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f56,f106])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f53,f94])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
