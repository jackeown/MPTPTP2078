%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 353 expanded)
%              Number of leaves         :   39 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  499 (1076 expanded)
%              Number of equality atoms :  103 ( 243 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f72,f76,f91,f95,f108,f112,f117,f124,f146,f169,f192,f198,f218,f233,f270,f291,f296,f305,f341,f342,f421,f463,f493,f551,f552])).

fof(f552,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK2
    | sP5(sK4(sK2,sK1),sK2)
    | ~ sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f551,plain,
    ( spl7_46
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_16
    | spl7_25
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f358,f286,f231,f151,f70,f61,f549])).

fof(f549,plain,
    ( spl7_46
  <=> sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f61,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f70,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f151,plain,
    ( spl7_16
  <=> k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f231,plain,
    ( spl7_25
  <=> k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f286,plain,
    ( spl7_31
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f358,plain,
    ( sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_16
    | spl7_25
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f245,f287])).

fof(f287,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f286])).

fof(f245,plain,
    ( sP5(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_16
    | spl7_25 ),
    inference(subsumption_resolution,[],[f199,f244])).

fof(f244,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl7_16
    | spl7_25 ),
    inference(superposition,[],[f232,f152])).

fof(f152,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f232,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f231])).

fof(f199,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | sP5(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f134,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4(sK2,X0))
        | k2_relat_1(sK2) = X0
        | sP5(sK4(sK2,X0),sK2) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f87,plain,
    ( ! [X0] :
        ( sP5(sK4(sK2,X0),sK2)
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f64,f86])).

fof(f86,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | sP5(sK4(sK2,X0),sK2)
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl7_1 ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(sK4(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f62,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f493,plain,
    ( spl7_16
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f377,f122,f110,f151])).

fof(f110,plain,
    ( spl7_10
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f122,plain,
    ( spl7_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f377,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(superposition,[],[f111,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f111,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f463,plain,
    ( spl7_20
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f373,f122,f70,f177])).

fof(f177,plain,
    ( spl7_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f373,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(superposition,[],[f71,f123])).

fof(f421,plain,
    ( spl7_23
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | spl7_23
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f411,f51])).

fof(f411,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(sK4(sK2,sK1)))
    | spl7_23
    | ~ spl7_32 ),
    inference(superposition,[],[f197,f290])).

fof(f290,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl7_32
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f197,plain,
    ( ~ r1_tarski(sK0,sK3(sK4(sK2,sK1)))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_23
  <=> r1_tarski(sK0,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f342,plain,
    ( sK4(sK2,sK1) != k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | sP5(sK4(sK2,sK1),sK2)
    | ~ sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f341,plain,
    ( ~ spl7_6
    | spl7_27
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl7_6
    | spl7_27
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f337,f269])).

fof(f269,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_27
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f337,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl7_6
    | ~ spl7_33 ),
    inference(resolution,[],[f295,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f94,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_6
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f295,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl7_33
  <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f305,plain,
    ( spl7_34
    | spl7_22
    | ~ spl7_1
    | ~ spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f144,f115,f70,f61,f190,f303])).

fof(f303,plain,
    ( spl7_34
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f190,plain,
    ( spl7_22
  <=> sP5(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f115,plain,
    ( spl7_11
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f144,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_3
    | spl7_11 ),
    inference(subsumption_resolution,[],[f137,f116])).

fof(f116,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f137,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f26])).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f296,plain,
    ( spl7_33
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f264,f190,f89,f61,f294])).

fof(f89,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f264,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f263,f90])).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f263,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f258,f62])).

fof(f258,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl7_22 ),
    inference(resolution,[],[f191,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f191,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f190])).

fof(f291,plain,
    ( spl7_31
    | spl7_32
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f242,f177,f167,f289,f286])).

fof(f167,plain,
    ( spl7_18
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f242,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f234,f168])).

fof(f168,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f234,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_20 ),
    inference(resolution,[],[f178,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f270,plain,
    ( ~ spl7_27
    | ~ spl7_1
    | ~ spl7_5
    | spl7_11
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f261,f190,f115,f89,f61,f268])).

fof(f261,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl7_1
    | ~ spl7_5
    | spl7_11
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f260,f116])).

fof(f260,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f259,f90])).

fof(f259,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f255,f62])).

fof(f255,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl7_22 ),
    inference(resolution,[],[f191,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f233,plain,
    ( ~ spl7_25
    | spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f157,f122,f74,f231])).

fof(f74,plain,
    ( spl7_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f157,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | spl7_4
    | ~ spl7_13 ),
    inference(superposition,[],[f75,f123])).

fof(f75,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f218,plain,
    ( spl7_24
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f193,f187,f126,f216])).

fof(f216,plain,
    ( spl7_24
  <=> sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f126,plain,
    ( spl7_14
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f187,plain,
    ( spl7_21
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f193,plain,
    ( sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2)
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(resolution,[],[f188,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sP5(k1_funct_1(sK2,X0),sK2) )
    | ~ spl7_14 ),
    inference(superposition,[],[f54,f127])).

fof(f127,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP5(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,
    ( r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f198,plain,
    ( ~ spl7_23
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f194,f187,f196])).

fof(f194,plain,
    ( ~ r1_tarski(sK0,sK3(sK4(sK2,sK1)))
    | ~ spl7_21 ),
    inference(resolution,[],[f188,f40])).

fof(f192,plain,
    ( spl7_21
    | spl7_22
    | ~ spl7_1
    | ~ spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f145,f115,f70,f61,f190,f187])).

fof(f145,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl7_1
    | ~ spl7_3
    | spl7_11 ),
    inference(subsumption_resolution,[],[f138,f116])).

fof(f138,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f25])).

fof(f25,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f169,plain,
    ( spl7_18
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f155,f122,f66,f167])).

fof(f66,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f155,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(superposition,[],[f67,f123])).

fof(f67,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f146,plain,
    ( spl7_14
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f128,f119,f106,f126])).

fof(f106,plain,
    ( spl7_9
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f119,plain,
    ( spl7_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(superposition,[],[f120,f107])).

fof(f107,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f120,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f124,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f84,f70,f66,f122,f119])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f79,f67])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f117,plain,
    ( ~ spl7_11
    | spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f113,f110,f74,f115])).

fof(f113,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl7_4
    | ~ spl7_10 ),
    inference(superposition,[],[f75,f111])).

fof(f112,plain,
    ( spl7_10
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f80,f70,f110])).

fof(f80,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f108,plain,
    ( spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f77,f70,f106])).

fof(f77,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,
    ( spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f85,f70,f93])).

fof(f85,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f91,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f86,f70,f89])).

fof(f76,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7561)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (7565)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (7568)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (7576)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (7571)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (7563)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (7564)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (7562)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (7566)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (7567)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (7562)Refutation not found, incomplete strategy% (7562)------------------------------
% 0.20/0.48  % (7562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7562)Memory used [KB]: 10618
% 0.20/0.48  % (7562)Time elapsed: 0.075 s
% 0.20/0.48  % (7562)------------------------------
% 0.20/0.48  % (7562)------------------------------
% 0.20/0.48  % (7573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (7572)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (7572)Refutation not found, incomplete strategy% (7572)------------------------------
% 0.20/0.48  % (7572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7561)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (7575)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (7578)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (7582)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (7570)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (7582)Refutation not found, incomplete strategy% (7582)------------------------------
% 0.20/0.49  % (7582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7582)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (7582)Memory used [KB]: 10618
% 0.20/0.49  % (7582)Time elapsed: 0.091 s
% 0.20/0.49  % (7582)------------------------------
% 0.20/0.49  % (7582)------------------------------
% 0.20/0.49  % (7569)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (7572)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7572)Memory used [KB]: 10618
% 0.20/0.50  % (7572)Time elapsed: 0.081 s
% 0.20/0.50  % (7572)------------------------------
% 0.20/0.50  % (7572)------------------------------
% 0.20/0.50  % (7581)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f553,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f63,f68,f72,f76,f91,f95,f108,f112,f117,f124,f146,f169,f192,f198,f218,f233,f270,f291,f296,f305,f341,f342,f421,f463,f493,f551,f552])).
% 0.20/0.50  fof(f552,plain,(
% 0.20/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != sK2 | sP5(sK4(sK2,sK1),sK2) | ~sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    spl7_46 | ~spl7_1 | ~spl7_3 | ~spl7_16 | spl7_25 | ~spl7_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f358,f286,f231,f151,f70,f61,f549])).
% 0.20/0.50  fof(f549,plain,(
% 0.20/0.50    spl7_46 <=> sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl7_1 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    spl7_16 <=> k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    spl7_25 <=> k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    spl7_31 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    sP5(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl7_1 | ~spl7_3 | ~spl7_16 | spl7_25 | ~spl7_31)),
% 0.20/0.50    inference(forward_demodulation,[],[f245,f287])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl7_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f286])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    sP5(sK4(sK2,k1_xboole_0),sK2) | (~spl7_1 | ~spl7_3 | ~spl7_16 | spl7_25)),
% 0.20/0.50    inference(subsumption_resolution,[],[f199,f244])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK2) | (~spl7_16 | spl7_25)),
% 0.20/0.50    inference(superposition,[],[f232,f152])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl7_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f151])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | spl7_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f231])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK2) | sP5(sK4(sK2,k1_xboole_0),sK2) | (~spl7_1 | ~spl7_3)),
% 0.20/0.50    inference(resolution,[],[f134,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK4(sK2,X0)) | k2_relat_1(sK2) = X0 | sP5(sK4(sK2,X0),sK2)) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.50    inference(resolution,[],[f87,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0] : (sP5(sK4(sK2,X0),sK2) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f64,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f71,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f70])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK2) | sP5(sK4(sK2,X0),sK2) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl7_1),
% 0.20/0.50    inference(resolution,[],[f62,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    spl7_16 | ~spl7_10 | ~spl7_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f377,f122,f110,f151])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    spl7_10 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl7_13 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.50  fof(f377,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | (~spl7_10 | ~spl7_13)),
% 0.20/0.50    inference(superposition,[],[f111,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl7_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f110])).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    spl7_20 | ~spl7_3 | ~spl7_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f373,f122,f70,f177])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    spl7_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_3 | ~spl7_13)),
% 0.20/0.50    inference(superposition,[],[f71,f123])).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    spl7_23 | ~spl7_32),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f420])).
% 0.20/0.50  fof(f420,plain,(
% 0.20/0.50    $false | (spl7_23 | ~spl7_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f411,f51])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,sK3(sK4(sK2,sK1))) | (spl7_23 | ~spl7_32)),
% 0.20/0.50    inference(superposition,[],[f197,f290])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl7_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f289])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    spl7_32 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ~r1_tarski(sK0,sK3(sK4(sK2,sK1))) | spl7_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    spl7_23 <=> r1_tarski(sK0,sK3(sK4(sK2,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    sK4(sK2,sK1) != k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | sP5(sK4(sK2,sK1),sK2) | ~sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    ~spl7_6 | spl7_27 | ~spl7_33),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f340])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    $false | (~spl7_6 | spl7_27 | ~spl7_33)),
% 0.20/0.50    inference(subsumption_resolution,[],[f337,f269])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK2,sK1),sK1) | spl7_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    spl7_27 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    r2_hidden(sK4(sK2,sK1),sK1) | (~spl7_6 | ~spl7_33)),
% 0.20/0.50    inference(resolution,[],[f295,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | ~spl7_6),
% 0.20/0.50    inference(resolution,[],[f94,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl7_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl7_6 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~spl7_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f294])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    spl7_33 <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    spl7_34 | spl7_22 | ~spl7_1 | ~spl7_3 | spl7_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f144,f115,f70,f61,f190,f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    spl7_34 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl7_22 <=> sP5(sK4(sK2,sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl7_11 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    sP5(sK4(sK2,sK1),sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl7_1 | ~spl7_3 | spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    sK1 != k2_relat_1(sK2) | spl7_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl7_1 | ~spl7_3)),
% 0.20/0.50    inference(resolution,[],[f87,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl7_33 | ~spl7_1 | ~spl7_5 | ~spl7_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f264,f190,f89,f61,f294])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl7_5 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_5 | ~spl7_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f263,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f89])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f258,f62])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~spl7_22),
% 0.20/0.50    inference(resolution,[],[f191,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~sP5(X2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    sP5(sK4(sK2,sK1),sK2) | ~spl7_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    spl7_31 | spl7_32 | ~spl7_18 | ~spl7_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f242,f177,f167,f289,f286])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    spl7_18 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl7_18 | ~spl7_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f234,f168])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f167])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_20),
% 0.20/0.50    inference(resolution,[],[f178,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f177])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~spl7_27 | ~spl7_1 | ~spl7_5 | spl7_11 | ~spl7_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f261,f190,f115,f89,f61,f268])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl7_1 | ~spl7_5 | spl7_11 | ~spl7_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f260,f116])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl7_1 | ~spl7_5 | ~spl7_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f90])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl7_1 | ~spl7_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f62])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~spl7_22),
% 0.20/0.50    inference(resolution,[],[f191,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~spl7_25 | spl7_4 | ~spl7_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f157,f122,f74,f231])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl7_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | (spl7_4 | ~spl7_13)),
% 0.20/0.50    inference(superposition,[],[f75,f123])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    spl7_24 | ~spl7_14 | ~spl7_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f193,f187,f126,f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl7_24 <=> sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl7_14 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    spl7_21 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    sP5(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),sK2) | (~spl7_14 | ~spl7_21)),
% 0.20/0.50    inference(resolution,[],[f188,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | sP5(k1_funct_1(sK2,X0),sK2)) ) | ~spl7_14),
% 0.20/0.50    inference(superposition,[],[f54,f127])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~spl7_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | sP5(k1_funct_1(X0,X3),X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    r2_hidden(sK3(sK4(sK2,sK1)),sK0) | ~spl7_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f187])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ~spl7_23 | ~spl7_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f194,f187,f196])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ~r1_tarski(sK0,sK3(sK4(sK2,sK1))) | ~spl7_21),
% 0.20/0.50    inference(resolution,[],[f188,f40])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl7_21 | spl7_22 | ~spl7_1 | ~spl7_3 | spl7_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f145,f115,f70,f61,f190,f187])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    sP5(sK4(sK2,sK1),sK2) | r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl7_1 | ~spl7_3 | spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f138,f116])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl7_1 | ~spl7_3)),
% 0.20/0.50    inference(resolution,[],[f87,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    spl7_18 | ~spl7_2 | ~spl7_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f155,f122,f66,f167])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl7_2 | ~spl7_13)),
% 0.20/0.50    inference(superposition,[],[f67,f123])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl7_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f66])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    spl7_14 | ~spl7_9 | ~spl7_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f128,f119,f106,f126])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl7_9 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl7_12 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | (~spl7_9 | ~spl7_12)),
% 0.20/0.50    inference(superposition,[],[f120,f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f106])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl7_12 | spl7_13 | ~spl7_2 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f84,f70,f66,f122,f119])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl7_2 | ~spl7_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f79,f67])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f71,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ~spl7_11 | spl7_4 | ~spl7_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f113,f110,f74,f115])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    sK1 != k2_relat_1(sK2) | (spl7_4 | ~spl7_10)),
% 0.20/0.50    inference(superposition,[],[f75,f111])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    spl7_10 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f80,f70,f110])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f71,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl7_9 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f77,f70,f106])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f71,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl7_6 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f70,f93])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl7_3),
% 0.20/0.50    inference(forward_demodulation,[],[f81,f80])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f71,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl7_5 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f86,f70,f89])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f74])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f70])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f66])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (7561)------------------------------
% 0.20/0.50  % (7561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7561)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (7561)Memory used [KB]: 6396
% 0.20/0.50  % (7561)Time elapsed: 0.076 s
% 0.20/0.50  % (7561)------------------------------
% 0.20/0.50  % (7561)------------------------------
% 0.20/0.50  % (7560)Success in time 0.146 s
%------------------------------------------------------------------------------
