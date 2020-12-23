%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:22 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 184 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  374 ( 648 expanded)
%              Number of equality atoms :   63 ( 104 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f153,f179,f219,f249,f256,f306,f325,f457,f552,f625,f969,f1190,f1222])).

fof(f1222,plain,
    ( ~ spl17_15
    | ~ spl17_56
    | ~ spl17_79 ),
    inference(avatar_contradiction_clause,[],[f1221])).

fof(f1221,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_56
    | ~ spl17_79 ),
    inference(trivial_inequality_removal,[],[f1209])).

fof(f1209,plain,
    ( sK4 != sK4
    | ~ spl17_15
    | ~ spl17_56
    | ~ spl17_79 ),
    inference(resolution,[],[f1202,f218])).

fof(f218,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl17_15
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f1202,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0 )
    | ~ spl17_56
    | ~ spl17_79 ),
    inference(duplicate_literal_removal,[],[f1201])).

fof(f1201,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) )
    | ~ spl17_56
    | ~ spl17_79 ),
    inference(resolution,[],[f1189,f968])).

fof(f968,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK9(sK3,X8,X9),sK0)
        | ~ r2_hidden(X9,k9_relat_1(sK3,X8)) )
    | ~ spl17_56 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl17_56
  <=> ! [X9,X8] :
        ( r2_hidden(sK9(sK3,X8,X9),sK0)
        | ~ r2_hidden(X9,k9_relat_1(sK3,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_56])])).

fof(f1189,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK3,sK2,X0),sK0)
        | sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) )
    | ~ spl17_79 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f1188,plain,
    ( spl17_79
  <=> ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(sK9(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_79])])).

fof(f1190,plain,
    ( ~ spl17_5
    | ~ spl17_1
    | spl17_79
    | ~ spl17_35 ),
    inference(avatar_split_clause,[],[f1039,f623,f1188,f123,f150])).

fof(f150,plain,
    ( spl17_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f123,plain,
    ( spl17_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f623,plain,
    ( spl17_35
  <=> ! [X3,X2] :
        ( sK4 != X3
        | ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | ~ m1_subset_1(sK9(sK3,X2,X3),sK0)
        | ~ r2_hidden(sK9(sK3,X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).

fof(f1039,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(sK9(sK3,sK2,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl17_35 ),
    inference(duplicate_literal_removal,[],[f1038])).

fof(f1038,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(sK9(sK3,sK2,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) )
    | ~ spl17_35 ),
    inference(resolution,[],[f647,f113])).

fof(f113,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f647,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(sK3,X1,X0),sK2)
        | sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK9(sK3,X1,X0),sK0) )
    | ~ spl17_35 ),
    inference(resolution,[],[f624,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f624,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK9(sK3,X2,X3),sK0)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | sK4 != X3
        | ~ r2_hidden(sK9(sK3,X2,X3),sK2) )
    | ~ spl17_35 ),
    inference(avatar_component_clause,[],[f623])).

fof(f969,plain,
    ( ~ spl17_5
    | ~ spl17_1
    | spl17_56
    | ~ spl17_21 ),
    inference(avatar_split_clause,[],[f566,f253,f967,f123,f150])).

fof(f253,plain,
    ( spl17_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_21])])).

fof(f566,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK9(sK3,X8,X9),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X9,k9_relat_1(sK3,X8)) )
    | ~ spl17_21 ),
    inference(superposition,[],[f114,f255])).

fof(f255,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl17_21 ),
    inference(avatar_component_clause,[],[f253])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK9(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f625,plain,
    ( ~ spl17_5
    | spl17_35 ),
    inference(avatar_split_clause,[],[f186,f623,f150])).

fof(f186,plain,(
    ! [X2,X3] :
      ( sK4 != X3
      | ~ r2_hidden(sK9(sK3,X2,X3),sK2)
      | ~ m1_subset_1(sK9(sK3,X2,X3),sK0)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X3,k9_relat_1(sK3,X2)) ) ),
    inference(global_subsumption,[],[f48,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( sK4 != X3
      | ~ r2_hidden(sK9(sK3,X2,X3),sK2)
      | ~ m1_subset_1(sK9(sK3,X2,X3),sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X3,k9_relat_1(sK3,X2)) ) ),
    inference(superposition,[],[f46,f112])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X3)) = X3
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK9(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f552,plain,(
    ~ spl17_31 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl17_31 ),
    inference(unit_resulting_resolution,[],[f51,f456,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f456,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl17_31 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl17_31
  <=> r2_hidden(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_31])])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f457,plain,
    ( spl17_31
    | ~ spl17_20
    | ~ spl17_24 ),
    inference(avatar_split_clause,[],[f446,f322,f246,f454])).

fof(f246,plain,
    ( spl17_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f322,plain,
    ( spl17_24
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f446,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl17_20
    | ~ spl17_24 ),
    inference(backward_demodulation,[],[f324,f248])).

fof(f248,plain,
    ( k1_xboole_0 = sK1
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f246])).

fof(f324,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f322])).

fof(f325,plain,
    ( spl17_24
    | ~ spl17_15
    | ~ spl17_23 ),
    inference(avatar_split_clause,[],[f312,f304,f216,f322])).

fof(f304,plain,
    ( spl17_23
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).

fof(f312,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl17_15
    | ~ spl17_23 ),
    inference(resolution,[],[f305,f218])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(X0,sK1) )
    | ~ spl17_23 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( ~ spl17_5
    | spl17_23
    | ~ spl17_10 ),
    inference(avatar_split_clause,[],[f231,f176,f304,f150])).

fof(f176,plain,
    ( spl17_10
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f204,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK16(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f204,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
        | r2_hidden(X4,sK1) )
    | ~ spl17_10 ),
    inference(resolution,[],[f189,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f189,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl17_10 ),
    inference(resolution,[],[f178,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f178,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f256,plain,
    ( ~ spl17_3
    | spl17_21
    | ~ spl17_19 ),
    inference(avatar_split_clause,[],[f250,f242,f253,f133])).

fof(f133,plain,
    ( spl17_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f242,plain,
    ( spl17_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f250,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl17_19 ),
    inference(superposition,[],[f244,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f244,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f242])).

fof(f249,plain,
    ( ~ spl17_2
    | spl17_19
    | spl17_20
    | ~ spl17_3 ),
    inference(avatar_split_clause,[],[f143,f133,f246,f242,f128])).

fof(f128,plain,
    ( spl17_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl17_3 ),
    inference(resolution,[],[f135,f101])).

fof(f101,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl17_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f219,plain,
    ( ~ spl17_3
    | spl17_15
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f155,f138,f216,f133])).

fof(f138,plain,
    ( spl17_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f155,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl17_4 ),
    inference(superposition,[],[f140,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f140,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f179,plain,
    ( spl17_10
    | ~ spl17_3 ),
    inference(avatar_split_clause,[],[f148,f133,f176])).

fof(f148,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl17_3 ),
    inference(resolution,[],[f135,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,
    ( spl17_5
    | ~ spl17_3 ),
    inference(avatar_split_clause,[],[f146,f133,f150])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl17_3 ),
    inference(resolution,[],[f135,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f141,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f47,f138])).

fof(f47,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,(
    spl17_3 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f131,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f49,f128])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    spl17_1 ),
    inference(avatar_split_clause,[],[f48,f123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:40:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.53  % (30298)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (30290)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (30306)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (30286)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30293)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (30287)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30282)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (30304)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (30295)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (30296)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (30285)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (30283)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (30310)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (30305)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (30284)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (30292)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (30288)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (30292)Refutation not found, incomplete strategy% (30292)------------------------------
% 0.22/0.55  % (30292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30292)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30292)Memory used [KB]: 10746
% 0.22/0.55  % (30292)Time elapsed: 0.134 s
% 0.22/0.55  % (30292)------------------------------
% 0.22/0.55  % (30292)------------------------------
% 0.22/0.56  % (30281)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (30302)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (30303)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (30294)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (30308)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (30300)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.56  % (30309)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.56  % (30301)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (30289)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.57  % (30297)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.58  % (30299)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.63/0.59  % (30291)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.63/0.59  % (30307)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.63/0.60  % (30291)Refutation not found, incomplete strategy% (30291)------------------------------
% 1.63/0.60  % (30291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (30291)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.61  
% 1.63/0.61  % (30291)Memory used [KB]: 10746
% 1.63/0.61  % (30291)Time elapsed: 0.154 s
% 1.63/0.61  % (30291)------------------------------
% 1.63/0.61  % (30291)------------------------------
% 2.10/0.65  % (30303)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.65  % SZS output start Proof for theBenchmark
% 2.10/0.65  fof(f1225,plain,(
% 2.10/0.65    $false),
% 2.10/0.65    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f153,f179,f219,f249,f256,f306,f325,f457,f552,f625,f969,f1190,f1222])).
% 2.10/0.65  fof(f1222,plain,(
% 2.10/0.65    ~spl17_15 | ~spl17_56 | ~spl17_79),
% 2.10/0.65    inference(avatar_contradiction_clause,[],[f1221])).
% 2.10/0.65  fof(f1221,plain,(
% 2.10/0.65    $false | (~spl17_15 | ~spl17_56 | ~spl17_79)),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f1209])).
% 2.10/0.65  fof(f1209,plain,(
% 2.10/0.65    sK4 != sK4 | (~spl17_15 | ~spl17_56 | ~spl17_79)),
% 2.10/0.65    inference(resolution,[],[f1202,f218])).
% 2.10/0.65  fof(f218,plain,(
% 2.10/0.65    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl17_15),
% 2.10/0.65    inference(avatar_component_clause,[],[f216])).
% 2.10/0.65  fof(f216,plain,(
% 2.10/0.65    spl17_15 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).
% 2.10/0.65  fof(f1202,plain,(
% 2.10/0.65    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK2)) | sK4 != X0) ) | (~spl17_56 | ~spl17_79)),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f1201])).
% 2.10/0.65  fof(f1201,plain,(
% 2.10/0.65    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(X0,k9_relat_1(sK3,sK2))) ) | (~spl17_56 | ~spl17_79)),
% 2.10/0.65    inference(resolution,[],[f1189,f968])).
% 2.10/0.65  fof(f968,plain,(
% 2.10/0.65    ( ! [X8,X9] : (r2_hidden(sK9(sK3,X8,X9),sK0) | ~r2_hidden(X9,k9_relat_1(sK3,X8))) ) | ~spl17_56),
% 2.10/0.65    inference(avatar_component_clause,[],[f967])).
% 2.10/0.65  fof(f967,plain,(
% 2.10/0.65    spl17_56 <=> ! [X9,X8] : (r2_hidden(sK9(sK3,X8,X9),sK0) | ~r2_hidden(X9,k9_relat_1(sK3,X8)))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_56])])).
% 2.10/0.65  fof(f1189,plain,(
% 2.10/0.65    ( ! [X0] : (~r2_hidden(sK9(sK3,sK2,X0),sK0) | sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2))) ) | ~spl17_79),
% 2.10/0.65    inference(avatar_component_clause,[],[f1188])).
% 2.10/0.65  fof(f1188,plain,(
% 2.10/0.65    spl17_79 <=> ! [X0] : (sK4 != X0 | ~r2_hidden(sK9(sK3,sK2,X0),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_79])])).
% 2.10/0.65  fof(f1190,plain,(
% 2.10/0.65    ~spl17_5 | ~spl17_1 | spl17_79 | ~spl17_35),
% 2.10/0.65    inference(avatar_split_clause,[],[f1039,f623,f1188,f123,f150])).
% 2.10/0.65  fof(f150,plain,(
% 2.10/0.65    spl17_5 <=> v1_relat_1(sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).
% 2.10/0.65  fof(f123,plain,(
% 2.10/0.65    spl17_1 <=> v1_funct_1(sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).
% 2.10/0.65  fof(f623,plain,(
% 2.10/0.65    spl17_35 <=> ! [X3,X2] : (sK4 != X3 | ~r2_hidden(X3,k9_relat_1(sK3,X2)) | ~m1_subset_1(sK9(sK3,X2,X3),sK0) | ~r2_hidden(sK9(sK3,X2,X3),sK2))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).
% 2.10/0.65  fof(f1039,plain,(
% 2.10/0.65    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK9(sK3,sK2,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl17_35),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f1038])).
% 2.10/0.65  fof(f1038,plain,(
% 2.10/0.65    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK9(sK3,sK2,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X0,k9_relat_1(sK3,sK2))) ) | ~spl17_35),
% 2.10/0.65    inference(resolution,[],[f647,f113])).
% 2.10/0.65  fof(f113,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 2.10/0.65    inference(equality_resolution,[],[f63])).
% 2.10/0.65  fof(f63,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 2.10/0.65    inference(cnf_transformation,[],[f29])).
% 2.10/0.65  fof(f29,plain,(
% 2.10/0.65    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/0.65    inference(flattening,[],[f28])).
% 2.10/0.65  fof(f28,plain,(
% 2.10/0.65    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f11])).
% 2.10/0.65  fof(f11,axiom,(
% 2.10/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 2.10/0.65  fof(f647,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r2_hidden(sK9(sK3,X1,X0),sK2) | sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK9(sK3,X1,X0),sK0)) ) | ~spl17_35),
% 2.10/0.65    inference(resolution,[],[f624,f76])).
% 2.10/0.65  fof(f76,plain,(
% 2.10/0.65    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f34])).
% 2.10/0.65  fof(f34,plain,(
% 2.10/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f6])).
% 2.10/0.65  fof(f6,axiom,(
% 2.10/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.10/0.65  fof(f624,plain,(
% 2.10/0.65    ( ! [X2,X3] : (~m1_subset_1(sK9(sK3,X2,X3),sK0) | ~r2_hidden(X3,k9_relat_1(sK3,X2)) | sK4 != X3 | ~r2_hidden(sK9(sK3,X2,X3),sK2)) ) | ~spl17_35),
% 2.10/0.65    inference(avatar_component_clause,[],[f623])).
% 2.10/0.65  fof(f969,plain,(
% 2.10/0.65    ~spl17_5 | ~spl17_1 | spl17_56 | ~spl17_21),
% 2.10/0.65    inference(avatar_split_clause,[],[f566,f253,f967,f123,f150])).
% 2.10/0.65  fof(f253,plain,(
% 2.10/0.65    spl17_21 <=> sK0 = k1_relat_1(sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_21])])).
% 2.10/0.65  fof(f566,plain,(
% 2.10/0.65    ( ! [X8,X9] : (r2_hidden(sK9(sK3,X8,X9),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X9,k9_relat_1(sK3,X8))) ) | ~spl17_21),
% 2.10/0.65    inference(superposition,[],[f114,f255])).
% 2.10/0.65  fof(f255,plain,(
% 2.10/0.65    sK0 = k1_relat_1(sK3) | ~spl17_21),
% 2.10/0.65    inference(avatar_component_clause,[],[f253])).
% 2.10/0.65  fof(f114,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 2.10/0.65    inference(equality_resolution,[],[f62])).
% 2.10/0.65  fof(f62,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK9(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 2.10/0.65    inference(cnf_transformation,[],[f29])).
% 2.10/0.65  fof(f625,plain,(
% 2.10/0.65    ~spl17_5 | spl17_35),
% 2.10/0.65    inference(avatar_split_clause,[],[f186,f623,f150])).
% 2.10/0.65  fof(f186,plain,(
% 2.10/0.65    ( ! [X2,X3] : (sK4 != X3 | ~r2_hidden(sK9(sK3,X2,X3),sK2) | ~m1_subset_1(sK9(sK3,X2,X3),sK0) | ~v1_relat_1(sK3) | ~r2_hidden(X3,k9_relat_1(sK3,X2))) )),
% 2.10/0.65    inference(global_subsumption,[],[f48,f182])).
% 2.10/0.65  fof(f182,plain,(
% 2.10/0.65    ( ! [X2,X3] : (sK4 != X3 | ~r2_hidden(sK9(sK3,X2,X3),sK2) | ~m1_subset_1(sK9(sK3,X2,X3),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X3,k9_relat_1(sK3,X2))) )),
% 2.10/0.65    inference(superposition,[],[f46,f112])).
% 2.10/0.65  fof(f112,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (k1_funct_1(X0,sK9(X0,X1,X3)) = X3 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 2.10/0.65    inference(equality_resolution,[],[f64])).
% 2.10/0.65  fof(f64,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK9(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 2.10/0.65    inference(cnf_transformation,[],[f29])).
% 2.10/0.65  fof(f46,plain,(
% 2.10/0.65    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f25,plain,(
% 2.10/0.65    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.10/0.65    inference(flattening,[],[f24])).
% 2.10/0.65  fof(f24,plain,(
% 2.10/0.65    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.10/0.65    inference(ennf_transformation,[],[f23])).
% 2.10/0.65  fof(f23,negated_conjecture,(
% 2.10/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.10/0.65    inference(negated_conjecture,[],[f22])).
% 2.10/0.65  fof(f22,conjecture,(
% 2.10/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 2.10/0.65  fof(f48,plain,(
% 2.10/0.65    v1_funct_1(sK3)),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f552,plain,(
% 2.10/0.65    ~spl17_31),
% 2.10/0.65    inference(avatar_contradiction_clause,[],[f550])).
% 2.10/0.65  fof(f550,plain,(
% 2.10/0.65    $false | ~spl17_31),
% 2.10/0.65    inference(unit_resulting_resolution,[],[f51,f456,f87])).
% 2.10/0.65  fof(f87,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f38])).
% 2.10/0.65  fof(f38,plain,(
% 2.10/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f14])).
% 2.10/0.65  fof(f14,axiom,(
% 2.10/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.10/0.65  fof(f456,plain,(
% 2.10/0.65    r2_hidden(sK4,k1_xboole_0) | ~spl17_31),
% 2.10/0.65    inference(avatar_component_clause,[],[f454])).
% 2.10/0.65  fof(f454,plain,(
% 2.10/0.65    spl17_31 <=> r2_hidden(sK4,k1_xboole_0)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_31])])).
% 2.10/0.65  fof(f51,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f4])).
% 2.10/0.65  fof(f4,axiom,(
% 2.10/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.10/0.65  fof(f457,plain,(
% 2.10/0.65    spl17_31 | ~spl17_20 | ~spl17_24),
% 2.10/0.65    inference(avatar_split_clause,[],[f446,f322,f246,f454])).
% 2.10/0.65  fof(f246,plain,(
% 2.10/0.65    spl17_20 <=> k1_xboole_0 = sK1),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).
% 2.10/0.65  fof(f322,plain,(
% 2.10/0.65    spl17_24 <=> r2_hidden(sK4,sK1)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).
% 2.10/0.65  fof(f446,plain,(
% 2.10/0.65    r2_hidden(sK4,k1_xboole_0) | (~spl17_20 | ~spl17_24)),
% 2.10/0.65    inference(backward_demodulation,[],[f324,f248])).
% 2.10/0.65  fof(f248,plain,(
% 2.10/0.65    k1_xboole_0 = sK1 | ~spl17_20),
% 2.10/0.65    inference(avatar_component_clause,[],[f246])).
% 2.10/0.65  fof(f324,plain,(
% 2.10/0.65    r2_hidden(sK4,sK1) | ~spl17_24),
% 2.10/0.65    inference(avatar_component_clause,[],[f322])).
% 2.10/0.65  fof(f325,plain,(
% 2.10/0.65    spl17_24 | ~spl17_15 | ~spl17_23),
% 2.10/0.65    inference(avatar_split_clause,[],[f312,f304,f216,f322])).
% 2.10/0.65  fof(f304,plain,(
% 2.10/0.65    spl17_23 <=> ! [X1,X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k9_relat_1(sK3,X1)))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).
% 2.10/0.65  fof(f312,plain,(
% 2.10/0.65    r2_hidden(sK4,sK1) | (~spl17_15 | ~spl17_23)),
% 2.10/0.65    inference(resolution,[],[f305,f218])).
% 2.10/0.65  fof(f305,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(X0,sK1)) ) | ~spl17_23),
% 2.10/0.65    inference(avatar_component_clause,[],[f304])).
% 2.10/0.65  fof(f306,plain,(
% 2.10/0.65    ~spl17_5 | spl17_23 | ~spl17_10),
% 2.10/0.65    inference(avatar_split_clause,[],[f231,f176,f304,f150])).
% 2.10/0.65  fof(f176,plain,(
% 2.10/0.65    spl17_10 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).
% 2.10/0.65  fof(f231,plain,(
% 2.10/0.65    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~v1_relat_1(sK3) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl17_10),
% 2.10/0.65    inference(resolution,[],[f204,f89])).
% 2.10/0.65  fof(f89,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK16(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f39])).
% 2.10/0.65  fof(f39,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.10/0.65    inference(ennf_transformation,[],[f10])).
% 2.10/0.65  fof(f10,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 2.10/0.65  fof(f204,plain,(
% 2.10/0.65    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK3) | r2_hidden(X4,sK1)) ) | ~spl17_10),
% 2.10/0.65    inference(resolution,[],[f189,f104])).
% 2.10/0.65  fof(f104,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f5])).
% 2.10/0.65  fof(f5,axiom,(
% 2.10/0.65    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.10/0.65  fof(f189,plain,(
% 2.10/0.65    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) ) | ~spl17_10),
% 2.10/0.65    inference(resolution,[],[f178,f82])).
% 2.10/0.65  fof(f82,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f37])).
% 2.10/0.65  fof(f37,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f2])).
% 2.10/0.65  fof(f2,axiom,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.10/0.65  fof(f178,plain,(
% 2.10/0.65    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl17_10),
% 2.10/0.65    inference(avatar_component_clause,[],[f176])).
% 2.10/0.65  fof(f256,plain,(
% 2.10/0.65    ~spl17_3 | spl17_21 | ~spl17_19),
% 2.10/0.65    inference(avatar_split_clause,[],[f250,f242,f253,f133])).
% 2.10/0.65  fof(f133,plain,(
% 2.10/0.65    spl17_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).
% 2.10/0.65  fof(f242,plain,(
% 2.10/0.65    spl17_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).
% 2.10/0.65  fof(f250,plain,(
% 2.10/0.65    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl17_19),
% 2.10/0.65    inference(superposition,[],[f244,f93])).
% 2.10/0.65  fof(f93,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f41])).
% 2.10/0.65  fof(f41,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.65    inference(ennf_transformation,[],[f18])).
% 2.10/0.65  fof(f18,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.10/0.65  fof(f244,plain,(
% 2.10/0.65    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl17_19),
% 2.10/0.65    inference(avatar_component_clause,[],[f242])).
% 2.10/0.65  fof(f249,plain,(
% 2.10/0.65    ~spl17_2 | spl17_19 | spl17_20 | ~spl17_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f143,f133,f246,f242,f128])).
% 2.10/0.65  fof(f128,plain,(
% 2.10/0.65    spl17_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).
% 2.10/0.65  fof(f143,plain,(
% 2.10/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl17_3),
% 2.10/0.65    inference(resolution,[],[f135,f101])).
% 2.10/0.65  fof(f101,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f44])).
% 2.10/0.65  fof(f44,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.65    inference(flattening,[],[f43])).
% 2.10/0.65  fof(f43,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.65    inference(ennf_transformation,[],[f20])).
% 2.10/0.65  fof(f20,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.10/0.65  fof(f135,plain,(
% 2.10/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl17_3),
% 2.10/0.65    inference(avatar_component_clause,[],[f133])).
% 2.10/0.65  fof(f219,plain,(
% 2.10/0.65    ~spl17_3 | spl17_15 | ~spl17_4),
% 2.10/0.65    inference(avatar_split_clause,[],[f155,f138,f216,f133])).
% 2.10/0.65  fof(f138,plain,(
% 2.10/0.65    spl17_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).
% 2.10/0.65  fof(f155,plain,(
% 2.10/0.65    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl17_4),
% 2.10/0.65    inference(superposition,[],[f140,f102])).
% 2.10/0.65  fof(f102,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f45,plain,(
% 2.10/0.65    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.65    inference(ennf_transformation,[],[f19])).
% 2.10/0.65  fof(f19,axiom,(
% 2.10/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.10/0.65  fof(f140,plain,(
% 2.10/0.65    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl17_4),
% 2.10/0.65    inference(avatar_component_clause,[],[f138])).
% 2.10/0.65  fof(f179,plain,(
% 2.10/0.65    spl17_10 | ~spl17_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f148,f133,f176])).
% 2.10/0.65  fof(f148,plain,(
% 2.10/0.65    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl17_3),
% 2.10/0.65    inference(resolution,[],[f135,f86])).
% 2.10/0.65  fof(f86,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f7])).
% 2.10/0.65  fof(f7,axiom,(
% 2.10/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.65  fof(f153,plain,(
% 2.10/0.65    spl17_5 | ~spl17_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f146,f133,f150])).
% 2.10/0.65  fof(f146,plain,(
% 2.10/0.65    v1_relat_1(sK3) | ~spl17_3),
% 2.10/0.65    inference(resolution,[],[f135,f92])).
% 2.10/0.65  fof(f92,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f40])).
% 2.10/0.65  fof(f40,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.65    inference(ennf_transformation,[],[f15])).
% 2.10/0.65  fof(f15,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.10/0.65  fof(f141,plain,(
% 2.10/0.65    spl17_4),
% 2.10/0.65    inference(avatar_split_clause,[],[f47,f138])).
% 2.10/0.65  fof(f47,plain,(
% 2.10/0.65    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f136,plain,(
% 2.10/0.65    spl17_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f50,f133])).
% 2.10/0.65  fof(f50,plain,(
% 2.10/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f131,plain,(
% 2.10/0.65    spl17_2),
% 2.10/0.65    inference(avatar_split_clause,[],[f49,f128])).
% 2.10/0.65  fof(f49,plain,(
% 2.10/0.65    v1_funct_2(sK3,sK0,sK1)),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f126,plain,(
% 2.10/0.65    spl17_1),
% 2.10/0.65    inference(avatar_split_clause,[],[f48,f123])).
% 2.10/0.65  % SZS output end Proof for theBenchmark
% 2.10/0.65  % (30303)------------------------------
% 2.10/0.65  % (30303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (30303)Termination reason: Refutation
% 2.10/0.65  
% 2.10/0.65  % (30303)Memory used [KB]: 11385
% 2.10/0.65  % (30303)Time elapsed: 0.218 s
% 2.10/0.65  % (30303)------------------------------
% 2.10/0.65  % (30303)------------------------------
% 2.10/0.65  % (30280)Success in time 0.279 s
%------------------------------------------------------------------------------
