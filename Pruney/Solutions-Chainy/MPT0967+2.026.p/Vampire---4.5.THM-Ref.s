%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 248 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  454 (1067 expanded)
%              Number of equality atoms :   95 ( 287 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f160,f188,f247,f315,f356,f376,f384,f404,f414,f425])).

fof(f425,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_20 ),
    inference(subsumption_resolution,[],[f421,f394])).

fof(f394,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f388,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f388,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(superposition,[],[f150,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f421,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_20 ),
    inference(resolution,[],[f413,f288])).

fof(f288,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f127,f287])).

fof(f287,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f286,f176])).

fof(f176,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f76,f114])).

fof(f76,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f286,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | r2_hidden(sK5(k1_xboole_0,X3),k1_xboole_0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f101,f115])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | r2_hidden(sK5(X1,X2),X1)
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f127,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f119,f115])).

fof(f119,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f413,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl6_20
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f414,plain,
    ( ~ spl6_20
    | ~ spl6_6
    | spl6_10 ),
    inference(avatar_split_clause,[],[f409,f181,f157,f411])).

fof(f157,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f181,plain,
    ( spl6_10
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f409,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl6_6
    | spl6_10 ),
    inference(forward_demodulation,[],[f183,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f183,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f181])).

fof(f404,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_11 ),
    inference(subsumption_resolution,[],[f402,f394])).

fof(f402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | spl6_11 ),
    inference(forward_demodulation,[],[f398,f115])).

fof(f398,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_6
    | spl6_11 ),
    inference(superposition,[],[f187,f159])).

fof(f187,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f384,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_11
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f382,f354])).

fof(f354,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl6_18
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f382,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_11 ),
    inference(forward_demodulation,[],[f378,f263])).

fof(f263,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f150,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f378,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f135,f155,f145,f150,f187,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f145,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f155,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f135,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f376,plain,
    ( ~ spl6_2
    | ~ spl6_13
    | ~ spl6_15
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_15
    | spl6_18 ),
    inference(subsumption_resolution,[],[f367,f321])).

fof(f321,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f140,f246,f314,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X0)
      | v5_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(f314,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_15
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f246,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f140,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f367,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ spl6_13
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f246,f355,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f355,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f353])).

fof(f356,plain,
    ( ~ spl6_18
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f302,f181,f153,f148,f143,f133,f353])).

fof(f302,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_10 ),
    inference(forward_demodulation,[],[f298,f263])).

fof(f298,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f135,f183,f155,f145,f150,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f315,plain,
    ( spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f218,f148,f312])).

fof(f218,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f150,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f247,plain,
    ( spl6_13
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f203,f148,f244])).

fof(f203,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f75,f150,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f188,plain,
    ( ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f124,f185,f181])).

fof(f124,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f68,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f68,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f160,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f67,f157,f153])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f65,f148])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f146,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f64,f143])).

fof(f64,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f141,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f138])).

fof(f66,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f136,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f63,f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (28474)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (28490)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (28471)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (28490)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (28487)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (28478)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f426,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f160,f188,f247,f315,f356,f376,f384,f404,f414,f425])).
% 0.22/0.52  fof(f425,plain,(
% 0.22/0.52    ~spl6_4 | ~spl6_5 | spl6_20),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f424])).
% 0.22/0.52  fof(f424,plain,(
% 0.22/0.52    $false | (~spl6_4 | ~spl6_5 | spl6_20)),
% 0.22/0.52    inference(subsumption_resolution,[],[f421,f394])).
% 0.22/0.52  fof(f394,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f388,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(flattening,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f388,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_4 | ~spl6_5)),
% 0.22/0.52    inference(superposition,[],[f150,f154])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl6_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f153])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl6_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f421,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl6_20),
% 0.22/0.52    inference(resolution,[],[f413,f288])).
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f287])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f286,f176])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f76,f114])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK5(k1_xboole_0,X3),k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 0.22/0.52    inference(superposition,[],[f101,f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f56])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r2_hidden(sK5(X1,X2),X1) | k1_relset_1(X1,X0,X2) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.52    inference(rectify,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.52    inference(nnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f119,f115])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl6_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f411])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    spl6_20 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.52  fof(f414,plain,(
% 0.22/0.52    ~spl6_20 | ~spl6_6 | spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f409,f181,f157,f411])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl6_6 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl6_10 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl6_6 | spl6_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f183,f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f157])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK0,sK2) | spl6_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f181])).
% 0.22/0.52  fof(f404,plain,(
% 0.22/0.52    ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_11),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f403])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    $false | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f402,f394])).
% 0.22/0.52  fof(f402,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_6 | spl6_11)),
% 0.22/0.52    inference(forward_demodulation,[],[f398,f115])).
% 0.22/0.52  fof(f398,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (~spl6_6 | spl6_11)),
% 0.22/0.52    inference(superposition,[],[f187,f159])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f185])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.52  fof(f384,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_11 | ~spl6_18),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f383])).
% 0.22/0.52  fof(f383,plain,(
% 0.22/0.52    $false | (~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_11 | ~spl6_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f382,f354])).
% 0.22/0.52  fof(f354,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK3),sK2) | ~spl6_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f353])).
% 0.22/0.52  fof(f353,plain,(
% 0.22/0.52    spl6_18 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.52  fof(f382,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_11)),
% 0.22/0.52    inference(forward_demodulation,[],[f378,f263])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f150,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f378,plain,(
% 0.22/0.52    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_11)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f135,f155,f145,f150,f187,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f143])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl6_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    k1_xboole_0 != sK1 | spl6_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f153])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f376,plain,(
% 0.22/0.52    ~spl6_2 | ~spl6_13 | ~spl6_15 | spl6_18),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f375])).
% 0.22/0.52  fof(f375,plain,(
% 0.22/0.52    $false | (~spl6_2 | ~spl6_13 | ~spl6_15 | spl6_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f367,f321])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    v5_relat_1(sK3,sK2) | (~spl6_2 | ~spl6_13 | ~spl6_15)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f140,f246,f314,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v5_relat_1(X2,X0) | v5_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    v5_relat_1(sK3,sK1) | ~spl6_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f312])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    spl6_15 <=> v5_relat_1(sK3,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl6_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f244])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    spl6_13 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2) | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl6_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f367,plain,(
% 0.22/0.52    ~v5_relat_1(sK3,sK2) | (~spl6_13 | spl6_18)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f246,f355,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f355,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | spl6_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f353])).
% 0.22/0.52  fof(f356,plain,(
% 0.22/0.52    ~spl6_18 | ~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f302,f181,f153,f148,f143,f133,f353])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f298,f263])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_4 | spl6_5 | spl6_10)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f135,f183,f155,f145,f150,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | v1_funct_2(X3,X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f47])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    spl6_15 | ~spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f218,f148,f312])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    v5_relat_1(sK3,sK1) | ~spl6_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f150,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    spl6_13 | ~spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f203,f148,f244])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl6_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f75,f150,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ~spl6_10 | ~spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f124,f185,f181])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f68,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f24])).
% 0.22/0.52  fof(f24,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ~spl6_5 | spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f67,f157,f153])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f65,f148])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f143])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f66,f138])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f49])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f63,f133])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28490)------------------------------
% 0.22/0.52  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28490)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28490)Memory used [KB]: 10874
% 0.22/0.52  % (28490)Time elapsed: 0.087 s
% 0.22/0.52  % (28490)------------------------------
% 0.22/0.52  % (28490)------------------------------
% 0.22/0.53  % (28466)Success in time 0.163 s
%------------------------------------------------------------------------------
