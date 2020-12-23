%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0968+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 8.71s
% Output     : Refutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 235 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  487 (1116 expanded)
%              Number of equality atoms :  150 ( 359 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2430,f3400,f4973,f5081,f5234,f6400,f6675,f8536,f8730,f9862,f11027,f12203])).

fof(f12203,plain,
    ( ~ spl77_3
    | ~ spl77_199 ),
    inference(avatar_contradiction_clause,[],[f12202])).

fof(f12202,plain,
    ( $false
    | ~ spl77_3
    | ~ spl77_199 ),
    inference(subsumption_resolution,[],[f12201,f1920])).

fof(f1920,plain,(
    ~ r2_hidden(sK4,k1_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f1736])).

fof(f1736,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(sK2,sK3))
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f1494,f1735])).

fof(f1735,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK4,k1_funct_2(sK2,sK3))
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1494,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1493])).

fof(f1493,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1480])).

fof(f1480,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1479])).

fof(f1479,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f12201,plain,
    ( r2_hidden(sK4,k1_funct_2(sK2,sK3))
    | ~ spl77_3
    | ~ spl77_199 ),
    inference(forward_demodulation,[],[f12200,f4954])).

fof(f4954,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl77_199 ),
    inference(avatar_component_clause,[],[f4952])).

fof(f4952,plain,
    ( spl77_199
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_199])])).

fof(f12200,plain,
    ( r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),sK3))
    | ~ spl77_3 ),
    inference(subsumption_resolution,[],[f12199,f2527])).

fof(f2527,plain,
    ( v1_relat_1(sK4)
    | ~ spl77_3 ),
    inference(avatar_component_clause,[],[f2526])).

fof(f2526,plain,
    ( spl77_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_3])])).

fof(f12199,plain,
    ( r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),sK3))
    | ~ v1_relat_1(sK4)
    | ~ spl77_3 ),
    inference(subsumption_resolution,[],[f12144,f1916])).

fof(f1916,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f1736])).

fof(f12144,plain,
    ( r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl77_3 ),
    inference(resolution,[],[f5211,f2366])).

fof(f2366,plain,(
    ! [X7,X1] :
      ( r2_hidden(X7,k1_funct_2(k1_relat_1(X7),X1))
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(equality_resolution,[],[f2365])).

fof(f2365,plain,(
    ! [X2,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(k1_relat_1(X7),X1) != X2 ) ),
    inference(equality_resolution,[],[f2364])).

fof(f2364,plain,(
    ! [X6,X2,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(k1_relat_1(X7),X1) != X2 ) ),
    inference(equality_resolution,[],[f1935])).

fof(f1935,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | k1_relat_1(X7) != X0
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1747])).

fof(f1747,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK7(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1)
              & k1_relat_1(sK8(X0,X1,X2)) = X0
              & sK7(X0,X1,X2) = sK8(X0,X1,X2)
              & v1_funct_1(sK8(X0,X1,X2))
              & v1_relat_1(sK8(X0,X1,X2)) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
                & k1_relat_1(sK9(X0,X1,X6)) = X0
                & sK9(X0,X1,X6) = X6
                & v1_funct_1(sK9(X0,X1,X6))
                & v1_relat_1(sK9(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f1743,f1746,f1745,f1744])).

fof(f1744,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK7(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK7(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1745,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK7(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1)
        & k1_relat_1(sK8(X0,X1,X2)) = X0
        & sK7(X0,X1,X2) = sK8(X0,X1,X2)
        & v1_funct_1(sK8(X0,X1,X2))
        & v1_relat_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1746,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
        & k1_relat_1(sK9(X0,X1,X6)) = X0
        & sK9(X0,X1,X6) = X6
        & v1_funct_1(sK9(X0,X1,X6))
        & v1_relat_1(sK9(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1743,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1742])).

fof(f1742,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1472])).

fof(f1472,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f5211,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl77_3 ),
    inference(subsumption_resolution,[],[f5176,f2527])).

fof(f5176,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f3144,f2317])).

fof(f2317,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1904,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1712])).

fof(f1712,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f3144,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f1918,f2326])).

fof(f2326,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1719])).

fof(f1719,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1918,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f1736])).

fof(f11027,plain,
    ( spl77_199
    | ~ spl77_197 ),
    inference(avatar_split_clause,[],[f11026,f4935,f4952])).

fof(f4935,plain,
    ( spl77_197
  <=> sK2 = k1_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_197])])).

fof(f11026,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl77_197 ),
    inference(subsumption_resolution,[],[f10998,f1918])).

fof(f10998,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl77_197 ),
    inference(superposition,[],[f4937,f2299])).

fof(f2299,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1690])).

fof(f1690,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f4937,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | ~ spl77_197 ),
    inference(avatar_component_clause,[],[f4935])).

fof(f9862,plain,
    ( ~ spl77_121
    | spl77_171
    | ~ spl77_215 ),
    inference(avatar_split_clause,[],[f9861,f6430,f4332,f4004])).

fof(f4004,plain,
    ( spl77_121
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_121])])).

fof(f4332,plain,
    ( spl77_171
  <=> ! [X270] : r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X270)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_171])])).

fof(f6430,plain,
    ( spl77_215
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_215])])).

fof(f9861,plain,
    ( ! [X270] :
        ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X270))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl77_215 ),
    inference(subsumption_resolution,[],[f9860,f1944])).

fof(f1944,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f9860,plain,
    ( ! [X270] :
        ( ~ r1_tarski(k1_xboole_0,X270)
        | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X270))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl77_215 ),
    inference(forward_demodulation,[],[f9859,f2088])).

fof(f2088,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f9859,plain,
    ( ! [X270] :
        ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X270))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X270)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl77_215 ),
    inference(forward_demodulation,[],[f7036,f2087])).

fof(f2087,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f7036,plain,
    ( ! [X270] :
        ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X270))
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X270)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl77_215 ),
    inference(resolution,[],[f6431,f2366])).

fof(f6431,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl77_215 ),
    inference(avatar_component_clause,[],[f6430])).

fof(f8730,plain,
    ( ~ spl77_76
    | spl77_302 ),
    inference(avatar_split_clause,[],[f8699,f8196,f2829])).

fof(f2829,plain,
    ( spl77_76
  <=> m1_subset_1(sK4,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_76])])).

fof(f8196,plain,
    ( spl77_302
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_302])])).

fof(f8699,plain,
    ( ~ m1_subset_1(sK4,k1_tarski(k1_xboole_0))
    | spl77_302 ),
    inference(forward_demodulation,[],[f8615,f2163])).

fof(f2163,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f8615,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | spl77_302 ),
    inference(resolution,[],[f8197,f1948])).

fof(f1948,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1752])).

fof(f1752,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f8197,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl77_302 ),
    inference(avatar_component_clause,[],[f8196])).

fof(f8536,plain,
    ( spl77_107
    | ~ spl77_302 ),
    inference(avatar_contradiction_clause,[],[f8535])).

fof(f8535,plain,
    ( $false
    | spl77_107
    | ~ spl77_302 ),
    inference(subsumption_resolution,[],[f8534,f1944])).

fof(f8534,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl77_107
    | ~ spl77_302 ),
    inference(subsumption_resolution,[],[f8422,f3323])).

fof(f3323,plain,
    ( k1_xboole_0 != sK4
    | spl77_107 ),
    inference(avatar_component_clause,[],[f3322])).

fof(f3322,plain,
    ( spl77_107
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_107])])).

fof(f8422,plain,
    ( k1_xboole_0 = sK4
    | ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl77_302 ),
    inference(resolution,[],[f8198,f2054])).

fof(f2054,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1787])).

fof(f1787,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1786])).

fof(f1786,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f8198,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl77_302 ),
    inference(avatar_component_clause,[],[f8196])).

fof(f6675,plain,(
    spl77_215 ),
    inference(avatar_contradiction_clause,[],[f6674])).

fof(f6674,plain,
    ( $false
    | spl77_215 ),
    inference(subsumption_resolution,[],[f6601,f2002])).

fof(f2002,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

fof(f6601,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl77_215 ),
    inference(resolution,[],[f6432,f1986])).

fof(f1986,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1538])).

fof(f1538,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f6432,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl77_215 ),
    inference(avatar_component_clause,[],[f6430])).

fof(f6400,plain,
    ( ~ spl77_2
    | ~ spl77_107
    | ~ spl77_171 ),
    inference(avatar_contradiction_clause,[],[f6399])).

fof(f6399,plain,
    ( $false
    | ~ spl77_2
    | ~ spl77_107
    | ~ spl77_171 ),
    inference(subsumption_resolution,[],[f6398,f4333])).

fof(f4333,plain,
    ( ! [X270] : r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X270))
    | ~ spl77_171 ),
    inference(avatar_component_clause,[],[f4332])).

fof(f6398,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,sK3))
    | ~ spl77_2
    | ~ spl77_107 ),
    inference(forward_demodulation,[],[f5096,f3324])).

fof(f3324,plain,
    ( k1_xboole_0 = sK4
    | ~ spl77_107 ),
    inference(avatar_component_clause,[],[f3322])).

fof(f5096,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(k1_xboole_0,sK3))
    | ~ spl77_2 ),
    inference(superposition,[],[f1920,f2429])).

fof(f2429,plain,
    ( k1_xboole_0 = sK2
    | ~ spl77_2 ),
    inference(avatar_component_clause,[],[f2427])).

fof(f2427,plain,
    ( spl77_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_2])])).

fof(f5234,plain,
    ( spl77_121
    | ~ spl77_107 ),
    inference(avatar_split_clause,[],[f5221,f3322,f4004])).

fof(f5221,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl77_107 ),
    inference(superposition,[],[f1916,f3324])).

fof(f5081,plain,
    ( ~ spl77_1
    | spl77_76 ),
    inference(avatar_contradiction_clause,[],[f5080])).

fof(f5080,plain,
    ( $false
    | ~ spl77_1
    | spl77_76 ),
    inference(subsumption_resolution,[],[f5079,f2831])).

fof(f2831,plain,
    ( ~ m1_subset_1(sK4,k1_tarski(k1_xboole_0))
    | spl77_76 ),
    inference(avatar_component_clause,[],[f2829])).

fof(f5079,plain,
    ( m1_subset_1(sK4,k1_tarski(k1_xboole_0))
    | ~ spl77_1 ),
    inference(forward_demodulation,[],[f5078,f2163])).

fof(f5078,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl77_1 ),
    inference(forward_demodulation,[],[f5075,f2374])).

fof(f2374,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1993])).

fof(f1993,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1774])).

fof(f1774,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1773])).

fof(f1773,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5075,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ spl77_1 ),
    inference(superposition,[],[f1918,f2424])).

fof(f2424,plain,
    ( k1_xboole_0 = sK3
    | ~ spl77_1 ),
    inference(avatar_component_clause,[],[f2423])).

fof(f2423,plain,
    ( spl77_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl77_1])])).

fof(f4973,plain,
    ( spl77_1
    | spl77_197 ),
    inference(avatar_split_clause,[],[f3214,f4935,f2423])).

fof(f3214,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f3114,f1917])).

fof(f1917,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f1736])).

fof(f3114,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | ~ v1_funct_2(sK4,sK2,sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f1918,f2026])).

fof(f2026,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1777])).

fof(f1777,plain,(
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
    inference(nnf_transformation,[],[f1557])).

fof(f1557,plain,(
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
    inference(flattening,[],[f1556])).

fof(f1556,plain,(
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
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
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

fof(f3400,plain,(
    spl77_3 ),
    inference(avatar_split_clause,[],[f3107,f2526])).

fof(f3107,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f1918,f1986])).

fof(f2430,plain,
    ( ~ spl77_1
    | spl77_2 ),
    inference(avatar_split_clause,[],[f1919,f2427,f2423])).

fof(f1919,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1736])).
%------------------------------------------------------------------------------
