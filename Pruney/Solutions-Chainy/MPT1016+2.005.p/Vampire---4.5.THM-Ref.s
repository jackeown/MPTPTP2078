%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 526 expanded)
%              Number of leaves         :   42 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  789 (3356 expanded)
%              Number of equality atoms :  178 ( 942 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f132,f227,f235,f239,f260,f266,f304,f305,f543,f575,f624,f727,f750,f756,f877,f1056,f1113])).

fof(f1113,plain,
    ( spl11_2
    | ~ spl11_50
    | ~ spl11_52 ),
    inference(avatar_contradiction_clause,[],[f1112])).

fof(f1112,plain,
    ( $false
    | spl11_2
    | ~ spl11_50
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f1100,f112])).

fof(f112,plain,
    ( sK6 != sK7
    | spl11_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_2
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1100,plain,
    ( sK6 = sK7
    | ~ spl11_50
    | ~ spl11_52 ),
    inference(backward_demodulation,[],[f719,f749])).

fof(f749,plain,
    ( sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl11_52
  <=> sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f719,plain,
    ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl11_50
  <=> sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1056,plain,
    ( ~ spl11_5
    | ~ spl11_51 ),
    inference(avatar_contradiction_clause,[],[f1055])).

fof(f1055,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1032,f202])).

fof(f202,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f178,f199])).

fof(f199,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f97,f84])).

fof(f84,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f178,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f177,f133])).

fof(f133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f83,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f177,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f85,f67])).

fof(f67,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1032,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | ~ spl11_5
    | ~ spl11_51 ),
    inference(backward_demodulation,[],[f308,f1020])).

fof(f1020,plain,
    ( k1_xboole_0 = sK4
    | ~ spl11_5
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1019,f127])).

fof(f127,plain,
    ( r2_hidden(sK6,sK4)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl11_5
  <=> r2_hidden(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1019,plain,
    ( ~ r2_hidden(sK6,sK4)
    | k1_xboole_0 = sK4
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1016,f60])).

fof(f60,plain,(
    v1_funct_2(sK5,sK4,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( sK6 != sK7
        & k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7)
        & r2_hidden(sK7,sK4)
        & r2_hidden(sK6,sK4) )
      | ~ v2_funct_1(sK5) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5)
          | ~ r2_hidden(X5,sK4)
          | ~ r2_hidden(X4,sK4) )
      | v2_funct_1(sK5) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    & v1_funct_2(sK5,sK4,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK5,X2) = k1_funct_1(sK5,X3)
            & r2_hidden(X3,sK4)
            & r2_hidden(X2,sK4) )
        | ~ v2_funct_1(sK5) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5)
            | ~ r2_hidden(X5,sK4)
            | ~ r2_hidden(X4,sK4) )
        | v2_funct_1(sK5) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
      & v1_funct_2(sK5,sK4,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK5,X2) = k1_funct_1(sK5,X3)
        & r2_hidden(X3,sK4)
        & r2_hidden(X2,sK4) )
   => ( sK6 != sK7
      & k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7)
      & r2_hidden(sK7,sK4)
      & r2_hidden(sK6,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f1016,plain,
    ( ~ v1_funct_2(sK5,sK4,sK4)
    | ~ r2_hidden(sK6,sK4)
    | k1_xboole_0 = sK4
    | ~ spl11_51 ),
    inference(resolution,[],[f745,f61])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f745,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK5,X3,X2)
        | ~ r2_hidden(sK6,X3)
        | k1_xboole_0 = X2 )
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f744])).

fof(f744,plain,
    ( spl11_51
  <=> ! [X3,X2] :
        ( k1_xboole_0 = X2
        | ~ v1_funct_2(sK5,X3,X2)
        | ~ r2_hidden(sK6,X3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f308,plain,
    ( ~ r1_tarski(sK4,sK6)
    | ~ spl11_5 ),
    inference(resolution,[],[f127,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f877,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f861,f202])).

fof(f861,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f308,f836])).

fof(f836,plain,
    ( k1_xboole_0 = sK4
    | ~ spl11_4
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f835,f122])).

fof(f122,plain,
    ( r2_hidden(sK7,sK4)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl11_4
  <=> r2_hidden(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f835,plain,
    ( ~ r2_hidden(sK7,sK4)
    | k1_xboole_0 = sK4
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f832,f60])).

fof(f832,plain,
    ( ~ v1_funct_2(sK5,sK4,sK4)
    | ~ r2_hidden(sK7,sK4)
    | k1_xboole_0 = sK4
    | ~ spl11_33 ),
    inference(resolution,[],[f570,f61])).

fof(f570,plain,
    ( ! [X21,X22] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
        | ~ v1_funct_2(sK5,X22,X21)
        | ~ r2_hidden(sK7,X22)
        | k1_xboole_0 = X21 )
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl11_33
  <=> ! [X22,X21] :
        ( k1_xboole_0 = X21
        | ~ v1_funct_2(sK5,X22,X21)
        | ~ r2_hidden(sK7,X22)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f756,plain,
    ( spl11_50
    | ~ spl11_24
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f755,f572,f332,f717])).

fof(f332,plain,
    ( spl11_24
  <=> k1_xboole_0 = k1_funct_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f572,plain,
    ( spl11_34
  <=> sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f755,plain,
    ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
    | ~ spl11_24
    | ~ spl11_34 ),
    inference(forward_demodulation,[],[f574,f334])).

fof(f334,plain,
    ( k1_xboole_0 = k1_funct_1(sK5,sK6)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f332])).

fof(f574,plain,
    ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f572])).

fof(f750,plain,
    ( spl11_51
    | spl11_52
    | ~ spl11_1
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f742,f332,f106,f747,f744])).

fof(f106,plain,
    ( spl11_1
  <=> v2_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f742,plain,
    ( ! [X2,X3] :
        ( sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK6,X3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK5,X3,X2) )
    | ~ spl11_1
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f741,f59])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f741,plain,
    ( ! [X2,X3] :
        ( sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK6,X3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK5,X3,X2)
        | ~ v1_funct_1(sK5) )
    | ~ spl11_1
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f735,f107])).

fof(f107,plain,
    ( v2_funct_1(sK5)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f735,plain,
    ( ! [X2,X3] :
        ( sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK6,X3)
        | ~ v2_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK5,X3,X2)
        | ~ v1_funct_1(sK5) )
    | ~ spl11_24 ),
    inference(superposition,[],[f99,f334])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f727,plain,(
    spl11_32 ),
    inference(avatar_contradiction_clause,[],[f726])).

fof(f726,plain,
    ( $false
    | spl11_32 ),
    inference(subsumption_resolution,[],[f725,f159])).

fof(f159,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f96,f61])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f725,plain,
    ( ~ v1_relat_1(sK5)
    | spl11_32 ),
    inference(subsumption_resolution,[],[f724,f59])).

fof(f724,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl11_32 ),
    inference(resolution,[],[f542,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP3(X2,X1,X0)
          & sP2(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f35,f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f542,plain,
    ( ~ sP3(k1_xboole_0,sK6,sK5)
    | spl11_32 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl11_32
  <=> sP3(k1_xboole_0,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f624,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_26
    | ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_26
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f622,f159])).

fof(f622,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_26
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f621,f59])).

fof(f621,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_26
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f620,f107])).

fof(f620,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl11_2
    | ~ spl11_26
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f619,f395])).

fof(f395,plain,
    ( r2_hidden(sK6,k1_relat_1(sK5))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl11_26
  <=> r2_hidden(sK6,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f619,plain,
    ( ~ r2_hidden(sK6,k1_relat_1(sK5))
    | ~ v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl11_2
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f586,f112])).

fof(f586,plain,
    ( sK6 = sK7
    | ~ r2_hidden(sK6,k1_relat_1(sK5))
    | ~ v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl11_34 ),
    inference(superposition,[],[f87,f574])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f575,plain,
    ( spl11_33
    | spl11_34
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f567,f115,f106,f572,f569])).

fof(f115,plain,
    ( spl11_3
  <=> k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f567,plain,
    ( ! [X21,X22] :
        ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6))
        | k1_xboole_0 = X21
        | ~ r2_hidden(sK7,X22)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
        | ~ v1_funct_2(sK5,X22,X21) )
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f566,f59])).

fof(f566,plain,
    ( ! [X21,X22] :
        ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6))
        | k1_xboole_0 = X21
        | ~ r2_hidden(sK7,X22)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
        | ~ v1_funct_2(sK5,X22,X21)
        | ~ v1_funct_1(sK5) )
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f557,f107])).

fof(f557,plain,
    ( ! [X21,X22] :
        ( sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6))
        | k1_xboole_0 = X21
        | ~ r2_hidden(sK7,X22)
        | ~ v2_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
        | ~ v1_funct_2(sK5,X22,X21)
        | ~ v1_funct_1(sK5) )
    | ~ spl11_3 ),
    inference(superposition,[],[f99,f117])).

fof(f117,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f543,plain,
    ( ~ spl11_32
    | spl11_26
    | spl11_24 ),
    inference(avatar_split_clause,[],[f533,f332,f394,f540])).

fof(f533,plain,
    ( r2_hidden(sK6,k1_relat_1(sK5))
    | ~ sP3(k1_xboole_0,sK6,sK5)
    | spl11_24 ),
    inference(trivial_inequality_removal,[],[f532])).

fof(f532,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK6,k1_relat_1(sK5))
    | ~ sP3(k1_xboole_0,sK6,sK5)
    | spl11_24 ),
    inference(superposition,[],[f333,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_funct_1(X2,X1)
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP3(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_xboole_0 != X0
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X2,X1) = X0
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | k1_funct_1(X2,X1) != X0 ) )
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | k1_funct_1(X0,X1) != X2 ) )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f333,plain,
    ( k1_xboole_0 != k1_funct_1(sK5,sK6)
    | spl11_24 ),
    inference(avatar_component_clause,[],[f332])).

fof(f305,plain,
    ( spl11_1
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f242,f216,f106])).

fof(f216,plain,
    ( spl11_11
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f242,plain,
    ( v2_funct_1(sK5)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f241,f59])).

fof(f241,plain,
    ( ~ v1_funct_1(sK5)
    | v2_funct_1(sK5)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f240,f159])).

fof(f240,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK5)
    | ~ spl11_11 ),
    inference(resolution,[],[f218,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f76,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f218,plain,
    ( sP0(sK5)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f304,plain,
    ( spl11_11
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f301,f257,f216])).

fof(f257,plain,
    ( spl11_16
  <=> sK9(sK5) = sK8(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f301,plain,
    ( sP0(sK5)
    | ~ spl11_16 ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,
    ( sK8(sK5) != sK8(sK5)
    | sP0(sK5)
    | ~ spl11_16 ),
    inference(superposition,[],[f75,f259])).

fof(f259,plain,
    ( sK9(sK5) = sK8(sK5)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f257])).

fof(f75,plain,(
    ! [X0] :
      ( sK8(X0) != sK9(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK8(X0) != sK9(X0)
          & k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0))
          & r2_hidden(sK9(X0),k1_relat_1(X0))
          & r2_hidden(sK8(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK8(X0) != sK9(X0)
        & k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0))
        & r2_hidden(sK9(X0),k1_relat_1(X0))
        & r2_hidden(sK8(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f266,plain,
    ( spl11_11
    | ~ spl11_14
    | spl11_15 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl11_11
    | ~ spl11_14
    | spl11_15 ),
    inference(subsumption_resolution,[],[f264,f217])).

fof(f217,plain,
    ( ~ sP0(sK5)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f264,plain,
    ( sP0(sK5)
    | ~ spl11_14
    | spl11_15 ),
    inference(subsumption_resolution,[],[f263,f233])).

fof(f233,plain,
    ( r1_tarski(k1_relat_1(sK5),sK4)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl11_14
  <=> r1_tarski(k1_relat_1(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f263,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),sK4)
    | sP0(sK5)
    | spl11_15 ),
    inference(resolution,[],[f261,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK5),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl11_15 ),
    inference(resolution,[],[f255,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f255,plain,
    ( ~ r2_hidden(sK8(sK5),sK4)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl11_15
  <=> r2_hidden(sK8(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f260,plain,
    ( ~ spl11_15
    | spl11_16
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f251,f224,f257,f253])).

fof(f224,plain,
    ( spl11_13
  <=> ! [X0] :
        ( k1_funct_1(sK5,X0) != k1_funct_1(sK5,sK8(sK5))
        | sK9(sK5) = X0
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f251,plain,
    ( sK9(sK5) = sK8(sK5)
    | ~ r2_hidden(sK8(sK5),sK4)
    | ~ spl11_13 ),
    inference(equality_resolution,[],[f225])).

fof(f225,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) != k1_funct_1(sK5,sK8(sK5))
        | sK9(sK5) = X0
        | ~ r2_hidden(X0,sK4) )
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f224])).

fof(f239,plain,(
    spl11_14 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl11_14 ),
    inference(subsumption_resolution,[],[f237,f159])).

fof(f237,plain,
    ( ~ v1_relat_1(sK5)
    | spl11_14 ),
    inference(subsumption_resolution,[],[f236,f198])).

fof(f198,plain,(
    v4_relat_1(sK5,sK4) ),
    inference(resolution,[],[f97,f61])).

fof(f236,plain,
    ( ~ v4_relat_1(sK5,sK4)
    | ~ v1_relat_1(sK5)
    | spl11_14 ),
    inference(resolution,[],[f234,f85])).

fof(f234,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),sK4)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( spl11_11
    | ~ spl11_14
    | spl11_12 ),
    inference(avatar_split_clause,[],[f229,f220,f232,f216])).

fof(f220,plain,
    ( spl11_12
  <=> r2_hidden(sK9(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f229,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),sK4)
    | sP0(sK5)
    | spl11_12 ),
    inference(resolution,[],[f228,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK5),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl11_12 ),
    inference(resolution,[],[f222,f89])).

fof(f222,plain,
    ( ~ r2_hidden(sK9(sK5),sK4)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f227,plain,
    ( spl11_11
    | ~ spl11_12
    | spl11_13
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f214,f130,f224,f220,f216])).

fof(f130,plain,
    ( spl11_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK4)
        | ~ r2_hidden(X5,sK4)
        | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f214,plain,
    ( ! [X1] :
        ( k1_funct_1(sK5,X1) != k1_funct_1(sK5,sK8(sK5))
        | ~ r2_hidden(sK9(sK5),sK4)
        | ~ r2_hidden(X1,sK4)
        | sK9(sK5) = X1
        | sP0(sK5) )
    | ~ spl11_6 ),
    inference(superposition,[],[f131,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f131,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5)
        | ~ r2_hidden(X4,sK4)
        | ~ r2_hidden(X5,sK4)
        | X4 = X5 )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f62,f130,f106])).

fof(f62,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5)
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X4,sK4)
      | v2_funct_1(sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f128,plain,
    ( ~ spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f63,f125,f106])).

fof(f63,plain,
    ( r2_hidden(sK6,sK4)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f64,f120,f106])).

fof(f64,plain,
    ( r2_hidden(sK7,sK4)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f65,f115,f106])).

fof(f65,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f66,f110,f106])).

fof(f66,plain,
    ( sK6 != sK7
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:13:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29822)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29814)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29808)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29823)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (29804)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29808)Refutation not found, incomplete strategy% (29808)------------------------------
% 0.21/0.52  % (29808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29815)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29808)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  % (29800)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  
% 0.21/0.53  % (29808)Memory used [KB]: 10746
% 0.21/0.53  % (29808)Time elapsed: 0.066 s
% 0.21/0.53  % (29808)------------------------------
% 0.21/0.53  % (29808)------------------------------
% 0.21/0.53  % (29799)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (29801)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29802)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29806)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (29809)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (29827)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (29820)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (29812)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (29803)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (29825)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (29824)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (29828)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (29803)Refutation not found, incomplete strategy% (29803)------------------------------
% 0.21/0.55  % (29803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29803)Memory used [KB]: 6268
% 0.21/0.55  % (29803)Time elapsed: 0.137 s
% 0.21/0.55  % (29803)------------------------------
% 0.21/0.55  % (29803)------------------------------
% 0.21/0.55  % (29818)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (29805)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (29817)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (29816)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (29813)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (29816)Refutation not found, incomplete strategy% (29816)------------------------------
% 0.21/0.56  % (29816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29816)Memory used [KB]: 10618
% 0.21/0.56  % (29816)Time elapsed: 0.149 s
% 0.21/0.56  % (29816)------------------------------
% 0.21/0.56  % (29816)------------------------------
% 0.21/0.56  % (29819)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (29809)Refutation not found, incomplete strategy% (29809)------------------------------
% 0.21/0.56  % (29809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29809)Memory used [KB]: 10746
% 0.21/0.56  % (29809)Time elapsed: 0.149 s
% 0.21/0.56  % (29809)------------------------------
% 0.21/0.56  % (29809)------------------------------
% 0.21/0.56  % (29811)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (29810)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (29810)Refutation not found, incomplete strategy% (29810)------------------------------
% 0.21/0.56  % (29810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29810)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29810)Memory used [KB]: 10746
% 0.21/0.56  % (29810)Time elapsed: 0.150 s
% 0.21/0.56  % (29810)------------------------------
% 0.21/0.56  % (29810)------------------------------
% 0.21/0.58  % (29807)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (29821)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  % (29826)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f1124,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f132,f227,f235,f239,f260,f266,f304,f305,f543,f575,f624,f727,f750,f756,f877,f1056,f1113])).
% 0.21/0.60  fof(f1113,plain,(
% 0.21/0.60    spl11_2 | ~spl11_50 | ~spl11_52),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f1112])).
% 0.21/0.60  fof(f1112,plain,(
% 0.21/0.60    $false | (spl11_2 | ~spl11_50 | ~spl11_52)),
% 0.21/0.60    inference(subsumption_resolution,[],[f1100,f112])).
% 0.21/0.60  fof(f112,plain,(
% 0.21/0.60    sK6 != sK7 | spl11_2),
% 0.21/0.60    inference(avatar_component_clause,[],[f110])).
% 0.21/0.60  fof(f110,plain,(
% 0.21/0.60    spl11_2 <=> sK6 = sK7),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.60  fof(f1100,plain,(
% 0.21/0.60    sK6 = sK7 | (~spl11_50 | ~spl11_52)),
% 0.21/0.60    inference(backward_demodulation,[],[f719,f749])).
% 0.21/0.60  fof(f749,plain,(
% 0.21/0.60    sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | ~spl11_52),
% 0.21/0.60    inference(avatar_component_clause,[],[f747])).
% 0.21/0.60  fof(f747,plain,(
% 0.21/0.60    spl11_52 <=> sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 0.21/0.60  fof(f719,plain,(
% 0.21/0.60    sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | ~spl11_50),
% 0.21/0.60    inference(avatar_component_clause,[],[f717])).
% 0.21/0.60  fof(f717,plain,(
% 0.21/0.60    spl11_50 <=> sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 0.21/0.60  fof(f1056,plain,(
% 0.21/0.60    ~spl11_5 | ~spl11_51),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f1055])).
% 0.21/0.60  fof(f1055,plain,(
% 0.21/0.60    $false | (~spl11_5 | ~spl11_51)),
% 0.21/0.60    inference(subsumption_resolution,[],[f1032,f202])).
% 0.21/0.60  fof(f202,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f178,f199])).
% 0.21/0.60  fof(f199,plain,(
% 0.21/0.60    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(resolution,[],[f97,f84])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).
% 0.21/0.60  fof(f97,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.60    inference(ennf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.60  fof(f178,plain,(
% 0.21/0.60    ( ! [X0] : (~v4_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f177,f133])).
% 0.21/0.60  fof(f133,plain,(
% 0.21/0.60    v1_relat_1(k1_xboole_0)),
% 0.21/0.60    inference(superposition,[],[f83,f103])).
% 0.21/0.60  fof(f103,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f94])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f58])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.60    inference(flattening,[],[f57])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.60    inference(nnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.60  fof(f83,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.60  fof(f177,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.60    inference(superposition,[],[f85,f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.60  fof(f1032,plain,(
% 0.21/0.60    ~r1_tarski(k1_xboole_0,sK6) | (~spl11_5 | ~spl11_51)),
% 0.21/0.60    inference(backward_demodulation,[],[f308,f1020])).
% 0.21/0.60  fof(f1020,plain,(
% 0.21/0.60    k1_xboole_0 = sK4 | (~spl11_5 | ~spl11_51)),
% 0.21/0.60    inference(subsumption_resolution,[],[f1019,f127])).
% 0.21/0.60  fof(f127,plain,(
% 0.21/0.60    r2_hidden(sK6,sK4) | ~spl11_5),
% 0.21/0.60    inference(avatar_component_clause,[],[f125])).
% 0.21/0.60  fof(f125,plain,(
% 0.21/0.60    spl11_5 <=> r2_hidden(sK6,sK4)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.60  fof(f1019,plain,(
% 0.21/0.60    ~r2_hidden(sK6,sK4) | k1_xboole_0 = sK4 | ~spl11_51),
% 0.21/0.60    inference(subsumption_resolution,[],[f1016,f60])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    v1_funct_2(sK5,sK4,sK4)),
% 0.21/0.60    inference(cnf_transformation,[],[f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ((sK6 != sK7 & k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7) & r2_hidden(sK7,sK4) & r2_hidden(sK6,sK4)) | ~v2_funct_1(sK5)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5) | ~r2_hidden(X5,sK4) | ~r2_hidden(X4,sK4)) | v2_funct_1(sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v1_funct_2(sK5,sK4,sK4) & v1_funct_1(sK5)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f39,f41,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK5,X2) = k1_funct_1(sK5,X3) & r2_hidden(X3,sK4) & r2_hidden(X2,sK4)) | ~v2_funct_1(sK5)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5) | ~r2_hidden(X5,sK4) | ~r2_hidden(X4,sK4)) | v2_funct_1(sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) & v1_funct_2(sK5,sK4,sK4) & v1_funct_1(sK5))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK5,X2) = k1_funct_1(sK5,X3) & r2_hidden(X3,sK4) & r2_hidden(X2,sK4)) => (sK6 != sK7 & k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7) & r2_hidden(sK7,sK4) & r2_hidden(sK6,sK4))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.60    inference(rectify,[],[f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.60    inference(flattening,[],[f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.60    inference(flattening,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.60    inference(negated_conjecture,[],[f14])).
% 0.21/0.60  fof(f14,conjecture,(
% 0.21/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.21/0.60  fof(f1016,plain,(
% 0.21/0.60    ~v1_funct_2(sK5,sK4,sK4) | ~r2_hidden(sK6,sK4) | k1_xboole_0 = sK4 | ~spl11_51),
% 0.21/0.60    inference(resolution,[],[f745,f61])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))),
% 0.21/0.60    inference(cnf_transformation,[],[f42])).
% 0.21/0.60  fof(f745,plain,(
% 0.21/0.60    ( ! [X2,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK5,X3,X2) | ~r2_hidden(sK6,X3) | k1_xboole_0 = X2) ) | ~spl11_51),
% 0.21/0.60    inference(avatar_component_clause,[],[f744])).
% 0.21/0.60  fof(f744,plain,(
% 0.21/0.60    spl11_51 <=> ! [X3,X2] : (k1_xboole_0 = X2 | ~v1_funct_2(sK5,X3,X2) | ~r2_hidden(sK6,X3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).
% 0.21/0.60  fof(f308,plain,(
% 0.21/0.60    ~r1_tarski(sK4,sK6) | ~spl11_5),
% 0.21/0.60    inference(resolution,[],[f127,f95])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.60  fof(f877,plain,(
% 0.21/0.60    ~spl11_4 | ~spl11_5 | ~spl11_33),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f876])).
% 0.21/0.60  fof(f876,plain,(
% 0.21/0.60    $false | (~spl11_4 | ~spl11_5 | ~spl11_33)),
% 0.21/0.60    inference(subsumption_resolution,[],[f861,f202])).
% 0.21/0.60  fof(f861,plain,(
% 0.21/0.60    ~r1_tarski(k1_xboole_0,sK6) | (~spl11_4 | ~spl11_5 | ~spl11_33)),
% 0.21/0.60    inference(backward_demodulation,[],[f308,f836])).
% 0.21/0.60  fof(f836,plain,(
% 0.21/0.60    k1_xboole_0 = sK4 | (~spl11_4 | ~spl11_33)),
% 0.21/0.60    inference(subsumption_resolution,[],[f835,f122])).
% 0.21/0.60  fof(f122,plain,(
% 0.21/0.60    r2_hidden(sK7,sK4) | ~spl11_4),
% 0.21/0.60    inference(avatar_component_clause,[],[f120])).
% 0.21/0.60  fof(f120,plain,(
% 0.21/0.60    spl11_4 <=> r2_hidden(sK7,sK4)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.60  fof(f835,plain,(
% 0.21/0.60    ~r2_hidden(sK7,sK4) | k1_xboole_0 = sK4 | ~spl11_33),
% 0.21/0.60    inference(subsumption_resolution,[],[f832,f60])).
% 0.21/0.60  fof(f832,plain,(
% 0.21/0.60    ~v1_funct_2(sK5,sK4,sK4) | ~r2_hidden(sK7,sK4) | k1_xboole_0 = sK4 | ~spl11_33),
% 0.21/0.60    inference(resolution,[],[f570,f61])).
% 0.21/0.60  fof(f570,plain,(
% 0.21/0.60    ( ! [X21,X22] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))) | ~v1_funct_2(sK5,X22,X21) | ~r2_hidden(sK7,X22) | k1_xboole_0 = X21) ) | ~spl11_33),
% 0.21/0.60    inference(avatar_component_clause,[],[f569])).
% 0.21/0.60  fof(f569,plain,(
% 0.21/0.60    spl11_33 <=> ! [X22,X21] : (k1_xboole_0 = X21 | ~v1_funct_2(sK5,X22,X21) | ~r2_hidden(sK7,X22) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 0.21/0.60  fof(f756,plain,(
% 0.21/0.60    spl11_50 | ~spl11_24 | ~spl11_34),
% 0.21/0.60    inference(avatar_split_clause,[],[f755,f572,f332,f717])).
% 0.21/0.60  fof(f332,plain,(
% 0.21/0.60    spl11_24 <=> k1_xboole_0 = k1_funct_1(sK5,sK6)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 0.21/0.60  fof(f572,plain,(
% 0.21/0.60    spl11_34 <=> sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 0.21/0.60  fof(f755,plain,(
% 0.21/0.60    sK7 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | (~spl11_24 | ~spl11_34)),
% 0.21/0.60    inference(forward_demodulation,[],[f574,f334])).
% 0.21/0.60  fof(f334,plain,(
% 0.21/0.60    k1_xboole_0 = k1_funct_1(sK5,sK6) | ~spl11_24),
% 0.21/0.60    inference(avatar_component_clause,[],[f332])).
% 0.21/0.60  fof(f574,plain,(
% 0.21/0.60    sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6)) | ~spl11_34),
% 0.21/0.60    inference(avatar_component_clause,[],[f572])).
% 0.21/0.60  fof(f750,plain,(
% 0.21/0.60    spl11_51 | spl11_52 | ~spl11_1 | ~spl11_24),
% 0.21/0.60    inference(avatar_split_clause,[],[f742,f332,f106,f747,f744])).
% 0.21/0.60  fof(f106,plain,(
% 0.21/0.60    spl11_1 <=> v2_funct_1(sK5)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.60  fof(f742,plain,(
% 0.21/0.60    ( ! [X2,X3] : (sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | k1_xboole_0 = X2 | ~r2_hidden(sK6,X3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK5,X3,X2)) ) | (~spl11_1 | ~spl11_24)),
% 0.21/0.60    inference(subsumption_resolution,[],[f741,f59])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    v1_funct_1(sK5)),
% 0.21/0.60    inference(cnf_transformation,[],[f42])).
% 0.21/0.60  fof(f741,plain,(
% 0.21/0.60    ( ! [X2,X3] : (sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | k1_xboole_0 = X2 | ~r2_hidden(sK6,X3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK5,X3,X2) | ~v1_funct_1(sK5)) ) | (~spl11_1 | ~spl11_24)),
% 0.21/0.60    inference(subsumption_resolution,[],[f735,f107])).
% 0.21/0.60  fof(f107,plain,(
% 0.21/0.60    v2_funct_1(sK5) | ~spl11_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f106])).
% 0.21/0.60  fof(f735,plain,(
% 0.21/0.60    ( ! [X2,X3] : (sK6 = k1_funct_1(k2_funct_1(sK5),k1_xboole_0) | k1_xboole_0 = X2 | ~r2_hidden(sK6,X3) | ~v2_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK5,X3,X2) | ~v1_funct_1(sK5)) ) | ~spl11_24),
% 0.21/0.60    inference(superposition,[],[f99,f334])).
% 0.21/0.60  fof(f99,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.60    inference(flattening,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.60    inference(ennf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.60  fof(f727,plain,(
% 0.21/0.60    spl11_32),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f726])).
% 0.21/0.60  fof(f726,plain,(
% 0.21/0.60    $false | spl11_32),
% 0.21/0.60    inference(subsumption_resolution,[],[f725,f159])).
% 0.21/0.60  fof(f159,plain,(
% 0.21/0.60    v1_relat_1(sK5)),
% 0.21/0.60    inference(resolution,[],[f96,f61])).
% 0.21/0.60  fof(f96,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.60    inference(ennf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.60  fof(f725,plain,(
% 0.21/0.60    ~v1_relat_1(sK5) | spl11_32),
% 0.21/0.60    inference(subsumption_resolution,[],[f724,f59])).
% 0.21/0.60  fof(f724,plain,(
% 0.21/0.60    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl11_32),
% 0.21/0.60    inference(resolution,[],[f542,f82])).
% 0.21/0.60  fof(f82,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(definition_folding,[],[f21,f35,f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP2(X0,X2,X1))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP3(X2,X1,X0))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(flattening,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.60  fof(f542,plain,(
% 0.21/0.60    ~sP3(k1_xboole_0,sK6,sK5) | spl11_32),
% 0.21/0.60    inference(avatar_component_clause,[],[f540])).
% 0.21/0.60  fof(f540,plain,(
% 0.21/0.60    spl11_32 <=> sP3(k1_xboole_0,sK6,sK5)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 0.21/0.60  fof(f624,plain,(
% 0.21/0.60    ~spl11_1 | spl11_2 | ~spl11_26 | ~spl11_34),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f623])).
% 0.21/0.60  fof(f623,plain,(
% 0.21/0.60    $false | (~spl11_1 | spl11_2 | ~spl11_26 | ~spl11_34)),
% 0.21/0.60    inference(subsumption_resolution,[],[f622,f159])).
% 0.21/0.60  fof(f622,plain,(
% 0.21/0.60    ~v1_relat_1(sK5) | (~spl11_1 | spl11_2 | ~spl11_26 | ~spl11_34)),
% 0.21/0.60    inference(subsumption_resolution,[],[f621,f59])).
% 0.21/0.60  fof(f621,plain,(
% 0.21/0.60    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (~spl11_1 | spl11_2 | ~spl11_26 | ~spl11_34)),
% 0.21/0.60    inference(subsumption_resolution,[],[f620,f107])).
% 0.21/0.60  fof(f620,plain,(
% 0.21/0.60    ~v2_funct_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (spl11_2 | ~spl11_26 | ~spl11_34)),
% 0.21/0.60    inference(subsumption_resolution,[],[f619,f395])).
% 0.21/0.60  fof(f395,plain,(
% 0.21/0.60    r2_hidden(sK6,k1_relat_1(sK5)) | ~spl11_26),
% 0.21/0.60    inference(avatar_component_clause,[],[f394])).
% 0.21/0.60  fof(f394,plain,(
% 0.21/0.60    spl11_26 <=> r2_hidden(sK6,k1_relat_1(sK5))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 0.21/0.60  fof(f619,plain,(
% 0.21/0.60    ~r2_hidden(sK6,k1_relat_1(sK5)) | ~v2_funct_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (spl11_2 | ~spl11_34)),
% 0.21/0.60    inference(subsumption_resolution,[],[f586,f112])).
% 0.21/0.60  fof(f586,plain,(
% 0.21/0.60    sK6 = sK7 | ~r2_hidden(sK6,k1_relat_1(sK5)) | ~v2_funct_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl11_34),
% 0.21/0.60    inference(superposition,[],[f87,f574])).
% 0.21/0.60  fof(f87,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(flattening,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.60  fof(f575,plain,(
% 0.21/0.60    spl11_33 | spl11_34 | ~spl11_1 | ~spl11_3),
% 0.21/0.60    inference(avatar_split_clause,[],[f567,f115,f106,f572,f569])).
% 0.21/0.60  fof(f115,plain,(
% 0.21/0.60    spl11_3 <=> k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.60  fof(f567,plain,(
% 0.21/0.60    ( ! [X21,X22] : (sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6)) | k1_xboole_0 = X21 | ~r2_hidden(sK7,X22) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))) | ~v1_funct_2(sK5,X22,X21)) ) | (~spl11_1 | ~spl11_3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f566,f59])).
% 0.21/0.60  fof(f566,plain,(
% 0.21/0.60    ( ! [X21,X22] : (sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6)) | k1_xboole_0 = X21 | ~r2_hidden(sK7,X22) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))) | ~v1_funct_2(sK5,X22,X21) | ~v1_funct_1(sK5)) ) | (~spl11_1 | ~spl11_3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f557,f107])).
% 0.21/0.60  fof(f557,plain,(
% 0.21/0.60    ( ! [X21,X22] : (sK7 = k1_funct_1(k2_funct_1(sK5),k1_funct_1(sK5,sK6)) | k1_xboole_0 = X21 | ~r2_hidden(sK7,X22) | ~v2_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X22,X21))) | ~v1_funct_2(sK5,X22,X21) | ~v1_funct_1(sK5)) ) | ~spl11_3),
% 0.21/0.60    inference(superposition,[],[f99,f117])).
% 0.21/0.60  fof(f117,plain,(
% 0.21/0.60    k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7) | ~spl11_3),
% 0.21/0.60    inference(avatar_component_clause,[],[f115])).
% 0.21/0.60  fof(f543,plain,(
% 0.21/0.60    ~spl11_32 | spl11_26 | spl11_24),
% 0.21/0.60    inference(avatar_split_clause,[],[f533,f332,f394,f540])).
% 0.21/0.60  fof(f533,plain,(
% 0.21/0.60    r2_hidden(sK6,k1_relat_1(sK5)) | ~sP3(k1_xboole_0,sK6,sK5) | spl11_24),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f532])).
% 0.21/0.60  fof(f532,plain,(
% 0.21/0.60    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK6,k1_relat_1(sK5)) | ~sP3(k1_xboole_0,sK6,sK5) | spl11_24),
% 0.21/0.60    inference(superposition,[],[f333,f100])).
% 0.21/0.60  fof(f100,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k1_xboole_0 = k1_funct_1(X2,X1) | r2_hidden(X1,k1_relat_1(X2)) | ~sP3(k1_xboole_0,X1,X2)) )),
% 0.21/0.60    inference(equality_resolution,[],[f78])).
% 0.21/0.60  fof(f78,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0 | r2_hidden(X1,k1_relat_1(X2)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f49])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (((k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0)) | r2_hidden(X1,k1_relat_1(X2)) | ~sP3(X0,X1,X2))),
% 0.21/0.60    inference(rectify,[],[f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ! [X2,X1,X0] : (((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0)) | ~sP3(X2,X1,X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f35])).
% 0.21/0.60  fof(f333,plain,(
% 0.21/0.60    k1_xboole_0 != k1_funct_1(sK5,sK6) | spl11_24),
% 0.21/0.60    inference(avatar_component_clause,[],[f332])).
% 0.21/0.60  fof(f305,plain,(
% 0.21/0.60    spl11_1 | ~spl11_11),
% 0.21/0.60    inference(avatar_split_clause,[],[f242,f216,f106])).
% 0.21/0.60  fof(f216,plain,(
% 0.21/0.60    spl11_11 <=> sP0(sK5)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.60  fof(f242,plain,(
% 0.21/0.60    v2_funct_1(sK5) | ~spl11_11),
% 0.21/0.60    inference(subsumption_resolution,[],[f241,f59])).
% 0.21/0.60  fof(f241,plain,(
% 0.21/0.60    ~v1_funct_1(sK5) | v2_funct_1(sK5) | ~spl11_11),
% 0.21/0.60    inference(subsumption_resolution,[],[f240,f159])).
% 0.21/0.60  fof(f240,plain,(
% 0.21/0.60    ~v1_relat_1(sK5) | ~v1_funct_1(sK5) | v2_funct_1(sK5) | ~spl11_11),
% 0.21/0.60    inference(resolution,[],[f218,f135])).
% 0.21/0.60  fof(f135,plain,(
% 0.21/0.60    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.60    inference(resolution,[],[f76,f70])).
% 0.21/0.60  fof(f70,plain,(
% 0.21/0.60    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(definition_folding,[],[f19,f32,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(flattening,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.60  fof(f218,plain,(
% 0.21/0.60    sP0(sK5) | ~spl11_11),
% 0.21/0.60    inference(avatar_component_clause,[],[f216])).
% 0.21/0.60  fof(f304,plain,(
% 0.21/0.60    spl11_11 | ~spl11_16),
% 0.21/0.60    inference(avatar_split_clause,[],[f301,f257,f216])).
% 0.21/0.60  fof(f257,plain,(
% 0.21/0.60    spl11_16 <=> sK9(sK5) = sK8(sK5)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.21/0.60  fof(f301,plain,(
% 0.21/0.60    sP0(sK5) | ~spl11_16),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f299])).
% 0.21/0.60  fof(f299,plain,(
% 0.21/0.60    sK8(sK5) != sK8(sK5) | sP0(sK5) | ~spl11_16),
% 0.21/0.60    inference(superposition,[],[f75,f259])).
% 0.21/0.60  fof(f259,plain,(
% 0.21/0.60    sK9(sK5) = sK8(sK5) | ~spl11_16),
% 0.21/0.60    inference(avatar_component_clause,[],[f257])).
% 0.21/0.60  fof(f75,plain,(
% 0.21/0.60    ( ! [X0] : (sK8(X0) != sK9(X0) | sP0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f47])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ! [X0] : ((sP0(X0) | (sK8(X0) != sK9(X0) & k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK8(X0) != sK9(X0) & k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.60    inference(rectify,[],[f44])).
% 1.95/0.63  fof(f44,plain,(
% 1.95/0.63    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.95/0.63    inference(nnf_transformation,[],[f31])).
% 1.95/0.63  fof(f266,plain,(
% 1.95/0.63    spl11_11 | ~spl11_14 | spl11_15),
% 1.95/0.63    inference(avatar_contradiction_clause,[],[f265])).
% 1.95/0.63  fof(f265,plain,(
% 1.95/0.63    $false | (spl11_11 | ~spl11_14 | spl11_15)),
% 1.95/0.63    inference(subsumption_resolution,[],[f264,f217])).
% 1.95/0.63  fof(f217,plain,(
% 1.95/0.63    ~sP0(sK5) | spl11_11),
% 1.95/0.63    inference(avatar_component_clause,[],[f216])).
% 1.95/0.63  fof(f264,plain,(
% 1.95/0.63    sP0(sK5) | (~spl11_14 | spl11_15)),
% 1.95/0.63    inference(subsumption_resolution,[],[f263,f233])).
% 1.95/0.63  fof(f233,plain,(
% 1.95/0.63    r1_tarski(k1_relat_1(sK5),sK4) | ~spl11_14),
% 1.95/0.63    inference(avatar_component_clause,[],[f232])).
% 1.95/0.63  fof(f232,plain,(
% 1.95/0.63    spl11_14 <=> r1_tarski(k1_relat_1(sK5),sK4)),
% 1.95/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.95/0.63  fof(f263,plain,(
% 1.95/0.63    ~r1_tarski(k1_relat_1(sK5),sK4) | sP0(sK5) | spl11_15),
% 1.95/0.63    inference(resolution,[],[f261,f72])).
% 1.95/0.63  fof(f72,plain,(
% 1.95/0.63    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f47])).
% 1.95/0.63  fof(f261,plain,(
% 1.95/0.63    ( ! [X0] : (~r2_hidden(sK8(sK5),X0) | ~r1_tarski(X0,sK4)) ) | spl11_15),
% 1.95/0.63    inference(resolution,[],[f255,f89])).
% 1.95/0.63  fof(f89,plain,(
% 1.95/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f56])).
% 1.95/0.63  fof(f56,plain,(
% 1.95/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).
% 1.95/0.63  fof(f55,plain,(
% 1.95/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 1.95/0.63    introduced(choice_axiom,[])).
% 1.95/0.63  fof(f54,plain,(
% 1.95/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/0.63    inference(rectify,[],[f53])).
% 1.95/0.63  fof(f53,plain,(
% 1.95/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.95/0.63    inference(nnf_transformation,[],[f25])).
% 1.95/0.63  fof(f25,plain,(
% 1.95/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.95/0.63    inference(ennf_transformation,[],[f1])).
% 1.95/0.63  fof(f1,axiom,(
% 1.95/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.95/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.95/0.63  fof(f255,plain,(
% 1.95/0.63    ~r2_hidden(sK8(sK5),sK4) | spl11_15),
% 1.95/0.63    inference(avatar_component_clause,[],[f253])).
% 1.95/0.63  fof(f253,plain,(
% 1.95/0.63    spl11_15 <=> r2_hidden(sK8(sK5),sK4)),
% 1.95/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.95/0.63  fof(f260,plain,(
% 1.95/0.63    ~spl11_15 | spl11_16 | ~spl11_13),
% 1.95/0.63    inference(avatar_split_clause,[],[f251,f224,f257,f253])).
% 1.95/0.63  fof(f224,plain,(
% 1.95/0.63    spl11_13 <=> ! [X0] : (k1_funct_1(sK5,X0) != k1_funct_1(sK5,sK8(sK5)) | sK9(sK5) = X0 | ~r2_hidden(X0,sK4))),
% 1.95/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.95/0.63  fof(f251,plain,(
% 1.95/0.63    sK9(sK5) = sK8(sK5) | ~r2_hidden(sK8(sK5),sK4) | ~spl11_13),
% 1.95/0.63    inference(equality_resolution,[],[f225])).
% 1.95/0.63  fof(f225,plain,(
% 1.95/0.63    ( ! [X0] : (k1_funct_1(sK5,X0) != k1_funct_1(sK5,sK8(sK5)) | sK9(sK5) = X0 | ~r2_hidden(X0,sK4)) ) | ~spl11_13),
% 1.95/0.63    inference(avatar_component_clause,[],[f224])).
% 1.95/0.63  fof(f239,plain,(
% 1.95/0.63    spl11_14),
% 1.95/0.63    inference(avatar_contradiction_clause,[],[f238])).
% 1.95/0.63  fof(f238,plain,(
% 1.95/0.63    $false | spl11_14),
% 1.95/0.63    inference(subsumption_resolution,[],[f237,f159])).
% 1.95/0.63  fof(f237,plain,(
% 1.95/0.63    ~v1_relat_1(sK5) | spl11_14),
% 1.95/0.63    inference(subsumption_resolution,[],[f236,f198])).
% 1.95/0.63  fof(f198,plain,(
% 1.95/0.63    v4_relat_1(sK5,sK4)),
% 1.95/0.63    inference(resolution,[],[f97,f61])).
% 1.95/0.63  fof(f236,plain,(
% 1.95/0.63    ~v4_relat_1(sK5,sK4) | ~v1_relat_1(sK5) | spl11_14),
% 1.95/0.63    inference(resolution,[],[f234,f85])).
% 1.95/0.63  fof(f234,plain,(
% 1.95/0.63    ~r1_tarski(k1_relat_1(sK5),sK4) | spl11_14),
% 1.95/0.63    inference(avatar_component_clause,[],[f232])).
% 1.95/0.63  fof(f235,plain,(
% 1.95/0.63    spl11_11 | ~spl11_14 | spl11_12),
% 1.95/0.63    inference(avatar_split_clause,[],[f229,f220,f232,f216])).
% 1.95/0.63  fof(f220,plain,(
% 1.95/0.63    spl11_12 <=> r2_hidden(sK9(sK5),sK4)),
% 1.95/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.95/0.63  fof(f229,plain,(
% 1.95/0.63    ~r1_tarski(k1_relat_1(sK5),sK4) | sP0(sK5) | spl11_12),
% 1.95/0.63    inference(resolution,[],[f228,f73])).
% 1.95/0.63  fof(f73,plain,(
% 1.95/0.63    ( ! [X0] : (r2_hidden(sK9(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f47])).
% 1.95/0.63  fof(f228,plain,(
% 1.95/0.63    ( ! [X0] : (~r2_hidden(sK9(sK5),X0) | ~r1_tarski(X0,sK4)) ) | spl11_12),
% 1.95/0.63    inference(resolution,[],[f222,f89])).
% 1.95/0.63  fof(f222,plain,(
% 1.95/0.63    ~r2_hidden(sK9(sK5),sK4) | spl11_12),
% 1.95/0.63    inference(avatar_component_clause,[],[f220])).
% 1.95/0.63  fof(f227,plain,(
% 1.95/0.63    spl11_11 | ~spl11_12 | spl11_13 | ~spl11_6),
% 1.95/0.63    inference(avatar_split_clause,[],[f214,f130,f224,f220,f216])).
% 1.95/0.63  fof(f130,plain,(
% 1.95/0.63    spl11_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK4) | ~r2_hidden(X5,sK4) | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5))),
% 1.95/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.95/0.63  fof(f214,plain,(
% 1.95/0.63    ( ! [X1] : (k1_funct_1(sK5,X1) != k1_funct_1(sK5,sK8(sK5)) | ~r2_hidden(sK9(sK5),sK4) | ~r2_hidden(X1,sK4) | sK9(sK5) = X1 | sP0(sK5)) ) | ~spl11_6),
% 1.95/0.63    inference(superposition,[],[f131,f74])).
% 1.95/0.63  fof(f74,plain,(
% 1.95/0.63    ( ! [X0] : (k1_funct_1(X0,sK8(X0)) = k1_funct_1(X0,sK9(X0)) | sP0(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f47])).
% 1.95/0.63  fof(f131,plain,(
% 1.95/0.63    ( ! [X4,X5] : (k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5) | ~r2_hidden(X4,sK4) | ~r2_hidden(X5,sK4) | X4 = X5) ) | ~spl11_6),
% 1.95/0.63    inference(avatar_component_clause,[],[f130])).
% 1.95/0.63  fof(f132,plain,(
% 1.95/0.63    spl11_1 | spl11_6),
% 1.95/0.63    inference(avatar_split_clause,[],[f62,f130,f106])).
% 1.95/0.63  fof(f62,plain,(
% 1.95/0.63    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK5,X4) != k1_funct_1(sK5,X5) | ~r2_hidden(X5,sK4) | ~r2_hidden(X4,sK4) | v2_funct_1(sK5)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f42])).
% 1.95/0.63  fof(f128,plain,(
% 1.95/0.63    ~spl11_1 | spl11_5),
% 1.95/0.63    inference(avatar_split_clause,[],[f63,f125,f106])).
% 1.95/0.63  fof(f63,plain,(
% 1.95/0.63    r2_hidden(sK6,sK4) | ~v2_funct_1(sK5)),
% 1.95/0.63    inference(cnf_transformation,[],[f42])).
% 1.95/0.63  fof(f123,plain,(
% 1.95/0.63    ~spl11_1 | spl11_4),
% 1.95/0.63    inference(avatar_split_clause,[],[f64,f120,f106])).
% 1.95/0.63  fof(f64,plain,(
% 1.95/0.63    r2_hidden(sK7,sK4) | ~v2_funct_1(sK5)),
% 1.95/0.63    inference(cnf_transformation,[],[f42])).
% 1.95/0.63  fof(f118,plain,(
% 1.95/0.63    ~spl11_1 | spl11_3),
% 1.95/0.63    inference(avatar_split_clause,[],[f65,f115,f106])).
% 1.95/0.63  fof(f65,plain,(
% 1.95/0.63    k1_funct_1(sK5,sK6) = k1_funct_1(sK5,sK7) | ~v2_funct_1(sK5)),
% 1.95/0.63    inference(cnf_transformation,[],[f42])).
% 1.95/0.63  fof(f113,plain,(
% 1.95/0.63    ~spl11_1 | ~spl11_2),
% 1.95/0.63    inference(avatar_split_clause,[],[f66,f110,f106])).
% 1.95/0.63  fof(f66,plain,(
% 1.95/0.63    sK6 != sK7 | ~v2_funct_1(sK5)),
% 1.95/0.63    inference(cnf_transformation,[],[f42])).
% 1.95/0.63  % SZS output end Proof for theBenchmark
% 1.95/0.63  % (29826)------------------------------
% 1.95/0.63  % (29826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.63  % (29826)Termination reason: Refutation
% 1.95/0.63  
% 1.95/0.63  % (29826)Memory used [KB]: 6780
% 1.95/0.63  % (29826)Time elapsed: 0.196 s
% 1.95/0.63  % (29826)------------------------------
% 1.95/0.63  % (29826)------------------------------
% 1.95/0.63  % (29798)Success in time 0.263 s
%------------------------------------------------------------------------------
