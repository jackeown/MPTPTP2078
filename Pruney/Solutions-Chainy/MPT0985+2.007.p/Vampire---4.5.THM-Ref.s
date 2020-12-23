%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  263 (1024 expanded)
%              Number of leaves         :   51 ( 382 expanded)
%              Depth                    :   14
%              Number of atoms          :  945 (3258 expanded)
%              Number of equality atoms :  136 ( 714 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f135,f153,f160,f169,f174,f183,f224,f229,f256,f278,f286,f291,f316,f327,f346,f355,f367,f435,f453,f480,f555,f571,f621,f626,f640,f732,f936,f998,f1023,f1264,f1274,f1275,f1291,f1311,f1320])).

fof(f1320,plain,
    ( ~ spl5_51
    | ~ spl5_68
    | spl5_91 ),
    inference(avatar_contradiction_clause,[],[f1319])).

fof(f1319,plain,
    ( $false
    | ~ spl5_51
    | ~ spl5_68
    | spl5_91 ),
    inference(subsumption_resolution,[],[f1318,f880])).

fof(f880,plain,
    ( m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl5_51
  <=> m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1318,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_68
    | spl5_91 ),
    inference(subsumption_resolution,[],[f1317,f1022])).

fof(f1022,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f1020,plain,
    ( spl5_68
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1317,plain,
    ( k1_xboole_0 != k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_91 ),
    inference(superposition,[],[f1310,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1310,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | spl5_91 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1308,plain,
    ( spl5_91
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f1311,plain,
    ( ~ spl5_91
    | spl5_43
    | ~ spl5_51
    | spl5_89 ),
    inference(avatar_split_clause,[],[f1304,f1288,f879,f637,f1308])).

fof(f637,plain,
    ( spl5_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1288,plain,
    ( spl5_89
  <=> v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f1304,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | spl5_43
    | ~ spl5_51
    | spl5_89 ),
    inference(subsumption_resolution,[],[f1303,f1290])).

fof(f1290,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_89 ),
    inference(avatar_component_clause,[],[f1288])).

fof(f1303,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_43
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f1300,f638])).

fof(f638,plain,
    ( k1_xboole_0 != sK0
    | spl5_43 ),
    inference(avatar_component_clause,[],[f637])).

fof(f1300,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))
    | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl5_51 ),
    inference(resolution,[],[f880,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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

fof(f1291,plain,
    ( ~ spl5_89
    | spl5_9
    | ~ spl5_26
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1279,f633,f364,f217,f1288])).

fof(f217,plain,
    ( spl5_9
  <=> v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f364,plain,
    ( spl5_26
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f633,plain,
    ( spl5_42
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1279,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_9
    | ~ spl5_26
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f402,f635])).

fof(f635,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f633])).

fof(f402,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl5_9
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f219,f366])).

fof(f366,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f364])).

fof(f219,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1275,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1274,plain,
    ( ~ spl5_56
    | ~ spl5_87 ),
    inference(avatar_contradiction_clause,[],[f1273])).

fof(f1273,plain,
    ( $false
    | ~ spl5_56
    | ~ spl5_87 ),
    inference(subsumption_resolution,[],[f1272,f935])).

fof(f935,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f933])).

fof(f933,plain,
    ( spl5_56
  <=> v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1272,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl5_87 ),
    inference(resolution,[],[f1263,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1263,plain,
    ( r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0))
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl5_87
  <=> r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f1264,plain,
    ( spl5_87
    | spl5_63 ),
    inference(avatar_split_clause,[],[f1024,f995,f1261])).

fof(f995,plain,
    ( spl5_63
  <=> r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f1024,plain,
    ( r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0))
    | spl5_63 ),
    inference(resolution,[],[f997,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f997,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_63 ),
    inference(avatar_component_clause,[],[f995])).

fof(f1023,plain,
    ( spl5_68
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f689,f633,f618,f1020])).

fof(f618,plain,
    ( spl5_39
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f689,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f620,f635])).

fof(f620,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f618])).

fof(f998,plain,
    ( ~ spl5_63
    | spl5_31
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f671,f633,f552,f995])).

fof(f552,plain,
    ( spl5_31
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f671,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_31
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f561,f635])).

fof(f561,plain,
    ( ~ r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_31 ),
    inference(resolution,[],[f554,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f554,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f552])).

fof(f936,plain,
    ( spl5_56
    | ~ spl5_23
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f651,f633,f338,f933])).

fof(f338,plain,
    ( spl5_23
  <=> v1_xboole_0(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f651,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl5_23
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f339,f635])).

fof(f339,plain,
    ( v1_xboole_0(k4_relat_1(sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f338])).

fof(f732,plain,
    ( ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_26
    | ~ spl5_34
    | spl5_40
    | ~ spl5_43 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_26
    | ~ spl5_34
    | spl5_40
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f727,f583])).

fof(f583,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_26
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f580,f521])).

fof(f521,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f494,f499])).

fof(f499,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f290,f482])).

fof(f482,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f335,f481])).

fof(f481,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f326,f427])).

fof(f427,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f326,f396])).

fof(f396,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f259,f366])).

fof(f259,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f257,f167])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f257,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_12 ),
    inference(superposition,[],[f82,f255])).

fof(f255,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_12
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f326,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_21
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f335,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f333,f315])).

fof(f315,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl5_20
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f333,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_21 ),
    inference(superposition,[],[f82,f326])).

fof(f290,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_18
  <=> sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f494,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f345,f481])).

fof(f345,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl5_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f580,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_34 ),
    inference(resolution,[],[f570,f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f570,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl5_34
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f727,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl5_40
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f625,f639])).

fof(f639,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f637])).

fof(f625,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl5_40 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl5_40
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f640,plain,
    ( spl5_42
    | spl5_43
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f528,f450,f364,f324,f313,f288,f253,f166,f157,f637,f633])).

fof(f157,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f450,plain,
    ( spl5_27
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f528,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f526,f503])).

fof(f503,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f159,f499])).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f526,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_27 ),
    inference(resolution,[],[f452,f123])).

fof(f123,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f452,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f450])).

fof(f626,plain,
    ( ~ spl5_40
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f525,f364,f360,f324,f313,f288,f253,f166,f623])).

fof(f360,plain,
    ( spl5_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f525,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | spl5_25
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f361,f499])).

fof(f361,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f360])).

fof(f621,plain,
    ( spl5_39
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f482,f364,f324,f313,f253,f166,f618])).

fof(f571,plain,
    ( spl5_34
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f515,f364,f324,f313,f288,f283,f253,f166,f568])).

fof(f283,plain,
    ( spl5_17
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f515,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f486,f499])).

fof(f486,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f285,f481])).

fof(f285,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f283])).

fof(f555,plain,
    ( ~ spl5_31
    | ~ spl5_6
    | spl5_10
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f505,f364,f324,f313,f288,f253,f221,f166,f552])).

fof(f221,plain,
    ( spl5_10
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f505,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_6
    | spl5_10
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f223,f499])).

fof(f223,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f480,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_21
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_21
    | ~ spl5_25 ),
    inference(global_subsumption,[],[f197,f228,f381,f380])).

fof(f380,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f305,f372])).

fof(f372,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f370,f159])).

fof(f370,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_25 ),
    inference(superposition,[],[f362,f110])).

fof(f362,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f360])).

fof(f305,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f242,f302])).

fof(f302,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f301,f167])).

fof(f301,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f300,f129])).

fof(f129,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f300,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(superposition,[],[f88,f277])).

fof(f277,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl5_16
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f242,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f241,f210])).

fof(f210,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f193,f205])).

fof(f205,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f203,f159])).

fof(f203,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(superposition,[],[f173,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f173,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f193,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f189,f188])).

fof(f188,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f145,f167])).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f139,f134])).

fof(f134,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f189,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f146,f167])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f140,f134])).

fof(f140,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f241,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f232,f194])).

fof(f194,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f190,f188])).

fof(f190,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f147,f167])).

fof(f147,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f141,f134])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f232,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl5_11 ),
    inference(resolution,[],[f228,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f381,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f306,f372])).

fof(f306,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f244,f302])).

fof(f244,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f243,f210])).

fof(f243,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f233,f194])).

fof(f233,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))
    | ~ spl5_11 ),
    inference(resolution,[],[f228,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f228,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_11
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f197,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f196,f188])).

fof(f196,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f192,f188])).

fof(f192,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f65,f188])).

fof(f65,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f453,plain,
    ( spl5_27
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f397,f364,f150,f450])).

fof(f150,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f397,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f152,f366])).

fof(f152,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f435,plain,
    ( spl5_15
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl5_15
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f405,f71])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f405,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_15
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f271,f366])).

fof(f271,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl5_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f367,plain,
    ( spl5_25
    | spl5_26
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f155,f150,f364,f360])).

fof(f155,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f154,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f154,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f152,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f355,plain,
    ( ~ spl5_15
    | ~ spl5_18
    | ~ spl5_20
    | spl5_23 ),
    inference(avatar_split_clause,[],[f351,f338,f313,f288,f270])).

fof(f351,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_18
    | ~ spl5_20
    | spl5_23 ),
    inference(forward_demodulation,[],[f350,f290])).

fof(f350,plain,
    ( ~ v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
    | ~ spl5_20
    | spl5_23 ),
    inference(subsumption_resolution,[],[f349,f315])).

fof(f349,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
    | spl5_23 ),
    inference(resolution,[],[f340,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f340,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f338])).

fof(f346,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f207,f171,f166,f157,f127,f343])).

fof(f207,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f185,f205])).

fof(f185,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f137,f167])).

fof(f137,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f87])).

fof(f327,plain,
    ( spl5_21
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f194,f166,f132,f127,f324])).

fof(f316,plain,
    ( spl5_20
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f302,f275,f166,f127,f313])).

fof(f291,plain,
    ( spl5_18
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f210,f171,f166,f157,f132,f127,f288])).

fof(f286,plain,
    ( spl5_17
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f206,f171,f166,f157,f127,f283])).

fof(f206,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f184,f205])).

fof(f184,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f136,f167])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f86])).

fof(f278,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f188,f166,f132,f127,f275])).

fof(f256,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f205,f171,f157,f253])).

fof(f229,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f198,f166,f162,f132,f127,f226])).

fof(f162,plain,
    ( spl5_5
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f198,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f164,f188])).

fof(f164,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f224,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f199,f166,f162,f132,f127,f221,f217])).

fof(f199,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f197,f198])).

fof(f183,plain,
    ( ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f159,f178])).

fof(f178,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_6 ),
    inference(resolution,[],[f168,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f168,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f174,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f70,f171])).

fof(f70,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f169,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f138,f127,f166,f162])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f129,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f160,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f68,f157])).

fof(f153,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f67,f150])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f135,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f69,f132])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f66,f127])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18350)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (18375)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (18361)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (18367)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (18353)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (18358)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18349)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18355)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (18348)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18351)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (18352)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18362)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (18373)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18359)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (18345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (18347)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (18369)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (18364)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (18368)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (18357)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18371)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (18370)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (18376)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (18374)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (18360)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (18372)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (18356)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (18354)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (18365)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (18363)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (18363)Refutation not found, incomplete strategy% (18363)------------------------------
% 0.21/0.56  % (18363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18363)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18363)Memory used [KB]: 10618
% 0.21/0.56  % (18363)Time elapsed: 0.160 s
% 0.21/0.56  % (18363)------------------------------
% 0.21/0.56  % (18363)------------------------------
% 0.21/0.58  % (18367)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1321,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f130,f135,f153,f160,f169,f174,f183,f224,f229,f256,f278,f286,f291,f316,f327,f346,f355,f367,f435,f453,f480,f555,f571,f621,f626,f640,f732,f936,f998,f1023,f1264,f1274,f1275,f1291,f1311,f1320])).
% 0.21/0.58  fof(f1320,plain,(
% 0.21/0.58    ~spl5_51 | ~spl5_68 | spl5_91),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1319])).
% 0.21/0.58  fof(f1319,plain,(
% 0.21/0.58    $false | (~spl5_51 | ~spl5_68 | spl5_91)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1318,f880])).
% 0.21/0.58  fof(f880,plain,(
% 0.21/0.58    m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl5_51),
% 0.21/0.58    inference(avatar_component_clause,[],[f879])).
% 0.21/0.58  fof(f879,plain,(
% 0.21/0.58    spl5_51 <=> m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.21/0.58  fof(f1318,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl5_68 | spl5_91)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1317,f1022])).
% 0.21/0.58  fof(f1022,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl5_68),
% 0.21/0.58    inference(avatar_component_clause,[],[f1020])).
% 0.21/0.58  fof(f1020,plain,(
% 0.21/0.58    spl5_68 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.58  fof(f1317,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relat_1(k4_relat_1(k1_xboole_0)) | ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl5_91),
% 0.21/0.58    inference(superposition,[],[f1310,f110])).
% 0.21/0.58  fof(f110,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.58  fof(f1310,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | spl5_91),
% 0.21/0.58    inference(avatar_component_clause,[],[f1308])).
% 0.21/0.58  fof(f1308,plain,(
% 0.21/0.58    spl5_91 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 0.21/0.58  fof(f1311,plain,(
% 0.21/0.58    ~spl5_91 | spl5_43 | ~spl5_51 | spl5_89),
% 0.21/0.58    inference(avatar_split_clause,[],[f1304,f1288,f879,f637,f1308])).
% 0.21/0.58  fof(f637,plain,(
% 0.21/0.58    spl5_43 <=> k1_xboole_0 = sK0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.58  fof(f1288,plain,(
% 0.21/0.58    spl5_89 <=> v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 0.21/0.58  fof(f1304,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | (spl5_43 | ~spl5_51 | spl5_89)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1303,f1290])).
% 0.21/0.58  fof(f1290,plain,(
% 0.21/0.58    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | spl5_89),
% 0.21/0.58    inference(avatar_component_clause,[],[f1288])).
% 0.21/0.58  fof(f1303,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl5_43 | ~spl5_51)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1300,f638])).
% 0.21/0.58  fof(f638,plain,(
% 0.21/0.58    k1_xboole_0 != sK0 | spl5_43),
% 0.21/0.58    inference(avatar_component_clause,[],[f637])).
% 0.21/0.58  fof(f1300,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~spl5_51),
% 0.21/0.58    inference(resolution,[],[f880,f117])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(flattening,[],[f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.58  fof(f1291,plain,(
% 0.21/0.58    ~spl5_89 | spl5_9 | ~spl5_26 | ~spl5_42),
% 0.21/0.58    inference(avatar_split_clause,[],[f1279,f633,f364,f217,f1288])).
% 0.21/0.58  fof(f217,plain,(
% 0.21/0.58    spl5_9 <=> v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.58  fof(f364,plain,(
% 0.21/0.58    spl5_26 <=> k1_xboole_0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.58  fof(f633,plain,(
% 0.21/0.58    spl5_42 <=> k1_xboole_0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.58  fof(f1279,plain,(
% 0.21/0.58    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl5_9 | ~spl5_26 | ~spl5_42)),
% 0.21/0.58    inference(forward_demodulation,[],[f402,f635])).
% 0.21/0.58  fof(f635,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl5_42),
% 0.21/0.58    inference(avatar_component_clause,[],[f633])).
% 0.21/0.58  fof(f402,plain,(
% 0.21/0.58    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | (spl5_9 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f219,f366])).
% 0.21/0.58  fof(f366,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~spl5_26),
% 0.21/0.58    inference(avatar_component_clause,[],[f364])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | spl5_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f217])).
% 0.21/0.58  fof(f1275,plain,(
% 0.21/0.58    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.58  fof(f1274,plain,(
% 0.21/0.58    ~spl5_56 | ~spl5_87),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1273])).
% 0.21/0.58  fof(f1273,plain,(
% 0.21/0.58    $false | (~spl5_56 | ~spl5_87)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1272,f935])).
% 0.21/0.58  fof(f935,plain,(
% 0.21/0.58    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl5_56),
% 0.21/0.58    inference(avatar_component_clause,[],[f933])).
% 0.21/0.58  fof(f933,plain,(
% 0.21/0.58    spl5_56 <=> v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.21/0.58  fof(f1272,plain,(
% 0.21/0.58    ~v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl5_87),
% 0.21/0.58    inference(resolution,[],[f1263,f95])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f1263,plain,(
% 0.21/0.58    r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0)) | ~spl5_87),
% 0.21/0.58    inference(avatar_component_clause,[],[f1261])).
% 0.21/0.58  fof(f1261,plain,(
% 0.21/0.58    spl5_87 <=> r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.21/0.58  fof(f1264,plain,(
% 0.21/0.58    spl5_87 | spl5_63),
% 0.21/0.58    inference(avatar_split_clause,[],[f1024,f995,f1261])).
% 0.21/0.58  fof(f995,plain,(
% 0.21/0.58    spl5_63 <=> r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.58  fof(f1024,plain,(
% 0.21/0.58    r2_hidden(sK4(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)),k4_relat_1(k1_xboole_0)) | spl5_63),
% 0.21/0.58    inference(resolution,[],[f997,f104])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f997,plain,(
% 0.21/0.58    ~r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | spl5_63),
% 0.21/0.58    inference(avatar_component_clause,[],[f995])).
% 0.21/0.58  fof(f1023,plain,(
% 0.21/0.58    spl5_68 | ~spl5_39 | ~spl5_42),
% 0.21/0.58    inference(avatar_split_clause,[],[f689,f633,f618,f1020])).
% 0.21/0.58  fof(f618,plain,(
% 0.21/0.58    spl5_39 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.58  fof(f689,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) | (~spl5_39 | ~spl5_42)),
% 0.21/0.58    inference(backward_demodulation,[],[f620,f635])).
% 0.21/0.58  fof(f620,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | ~spl5_39),
% 0.21/0.58    inference(avatar_component_clause,[],[f618])).
% 0.21/0.58  fof(f998,plain,(
% 0.21/0.58    ~spl5_63 | spl5_31 | ~spl5_42),
% 0.21/0.58    inference(avatar_split_clause,[],[f671,f633,f552,f995])).
% 0.21/0.58  fof(f552,plain,(
% 0.21/0.58    spl5_31 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.58  fof(f671,plain,(
% 0.21/0.58    ~r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | (spl5_31 | ~spl5_42)),
% 0.21/0.58    inference(backward_demodulation,[],[f561,f635])).
% 0.21/0.58  fof(f561,plain,(
% 0.21/0.58    ~r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k1_xboole_0,sK0)) | spl5_31),
% 0.21/0.58    inference(resolution,[],[f554,f106])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f554,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl5_31),
% 0.21/0.58    inference(avatar_component_clause,[],[f552])).
% 0.21/0.58  fof(f936,plain,(
% 0.21/0.58    spl5_56 | ~spl5_23 | ~spl5_42),
% 0.21/0.58    inference(avatar_split_clause,[],[f651,f633,f338,f933])).
% 0.21/0.58  fof(f338,plain,(
% 0.21/0.58    spl5_23 <=> v1_xboole_0(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.58  fof(f651,plain,(
% 0.21/0.58    v1_xboole_0(k4_relat_1(k1_xboole_0)) | (~spl5_23 | ~spl5_42)),
% 0.21/0.58    inference(backward_demodulation,[],[f339,f635])).
% 0.21/0.58  fof(f339,plain,(
% 0.21/0.58    v1_xboole_0(k4_relat_1(sK2)) | ~spl5_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f338])).
% 0.21/0.58  fof(f732,plain,(
% 0.21/0.58    ~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_24 | ~spl5_26 | ~spl5_34 | spl5_40 | ~spl5_43),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f731])).
% 0.21/0.58  fof(f731,plain,(
% 0.21/0.58    $false | (~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_24 | ~spl5_26 | ~spl5_34 | spl5_40 | ~spl5_43)),
% 0.21/0.58    inference(subsumption_resolution,[],[f727,f583])).
% 0.21/0.58  fof(f583,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_24 | ~spl5_26 | ~spl5_34)),
% 0.21/0.58    inference(subsumption_resolution,[],[f580,f521])).
% 0.21/0.58  fof(f521,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_24 | ~spl5_26)),
% 0.21/0.58    inference(forward_demodulation,[],[f494,f499])).
% 0.21/0.58  fof(f499,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | (~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f290,f482])).
% 0.21/0.58  fof(f482,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | (~spl5_6 | ~spl5_12 | ~spl5_20 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(subsumption_resolution,[],[f335,f481])).
% 0.21/0.58  fof(f481,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(sK2) | (~spl5_6 | ~spl5_12 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f326,f427])).
% 0.21/0.58  fof(f427,plain,(
% 0.21/0.58    k1_xboole_0 = k2_relat_1(k4_relat_1(sK2)) | (~spl5_6 | ~spl5_12 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f326,f396])).
% 0.21/0.58  fof(f396,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(sK2) | (~spl5_6 | ~spl5_12 | ~spl5_26)),
% 0.21/0.58    inference(subsumption_resolution,[],[f259,f366])).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(sK2) | (~spl5_6 | ~spl5_12)),
% 0.21/0.58    inference(subsumption_resolution,[],[f257,f167])).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    v1_relat_1(sK2) | ~spl5_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f166])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    spl5_6 <=> v1_relat_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.58  fof(f257,plain,(
% 0.21/0.58    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl5_12),
% 0.21/0.58    inference(superposition,[],[f82,f255])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    sK1 = k2_relat_1(sK2) | ~spl5_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f253])).
% 0.21/0.58  fof(f253,plain,(
% 0.21/0.58    spl5_12 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.58  fof(f326,plain,(
% 0.21/0.58    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl5_21),
% 0.21/0.58    inference(avatar_component_clause,[],[f324])).
% 0.21/0.58  fof(f324,plain,(
% 0.21/0.58    spl5_21 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.58  fof(f335,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | (~spl5_20 | ~spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f333,f315])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    v1_relat_1(k4_relat_1(sK2)) | ~spl5_20),
% 0.21/0.58    inference(avatar_component_clause,[],[f313])).
% 0.21/0.58  fof(f313,plain,(
% 0.21/0.58    spl5_20 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.58  fof(f333,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k4_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | ~spl5_21),
% 0.21/0.58    inference(superposition,[],[f82,f326])).
% 0.21/0.58  fof(f290,plain,(
% 0.21/0.58    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl5_18),
% 0.21/0.58    inference(avatar_component_clause,[],[f288])).
% 0.21/0.58  fof(f288,plain,(
% 0.21/0.58    spl5_18 <=> sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.58  fof(f494,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_6 | ~spl5_12 | ~spl5_21 | ~spl5_24 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f345,f481])).
% 0.21/0.58  fof(f345,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl5_24),
% 0.21/0.58    inference(avatar_component_clause,[],[f343])).
% 0.21/0.58  fof(f343,plain,(
% 0.21/0.58    spl5_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.58  fof(f580,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_34),
% 0.21/0.58    inference(resolution,[],[f570,f121])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.58    inference(equality_resolution,[],[f116])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f64])).
% 0.21/0.58  fof(f570,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl5_34),
% 0.21/0.58    inference(avatar_component_clause,[],[f568])).
% 0.21/0.58  fof(f568,plain,(
% 0.21/0.58    spl5_34 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.58  fof(f727,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl5_40 | ~spl5_43)),
% 0.21/0.58    inference(backward_demodulation,[],[f625,f639])).
% 0.21/0.58  fof(f639,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~spl5_43),
% 0.21/0.58    inference(avatar_component_clause,[],[f637])).
% 0.21/0.58  fof(f625,plain,(
% 0.21/0.58    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | spl5_40),
% 0.21/0.58    inference(avatar_component_clause,[],[f623])).
% 0.21/0.58  fof(f623,plain,(
% 0.21/0.58    spl5_40 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.58  fof(f640,plain,(
% 0.21/0.58    spl5_42 | spl5_43 | ~spl5_4 | ~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26 | ~spl5_27),
% 0.21/0.58    inference(avatar_split_clause,[],[f528,f450,f364,f324,f313,f288,f253,f166,f157,f637,f633])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.58  fof(f450,plain,(
% 0.21/0.58    spl5_27 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.58  fof(f528,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl5_4 | ~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26 | ~spl5_27)),
% 0.21/0.58    inference(subsumption_resolution,[],[f526,f503])).
% 0.21/0.58  fof(f503,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_4 | ~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f159,f499])).
% 0.21/0.58  fof(f159,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f157])).
% 0.21/0.58  fof(f526,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_27),
% 0.21/0.58    inference(resolution,[],[f452,f123])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.58    inference(equality_resolution,[],[f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f64])).
% 0.21/0.58  fof(f452,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl5_27),
% 0.21/0.58    inference(avatar_component_clause,[],[f450])).
% 0.21/0.58  fof(f626,plain,(
% 0.21/0.58    ~spl5_40 | ~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | spl5_25 | ~spl5_26),
% 0.21/0.58    inference(avatar_split_clause,[],[f525,f364,f360,f324,f313,f288,f253,f166,f623])).
% 0.21/0.58  fof(f360,plain,(
% 0.21/0.58    spl5_25 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.58  fof(f525,plain,(
% 0.21/0.58    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl5_6 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | spl5_25 | ~spl5_26)),
% 0.21/0.58    inference(forward_demodulation,[],[f361,f499])).
% 0.21/0.58  fof(f361,plain,(
% 0.21/0.58    sK0 != k1_relset_1(sK0,sK1,sK2) | spl5_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f360])).
% 0.21/0.58  fof(f621,plain,(
% 0.21/0.58    spl5_39 | ~spl5_6 | ~spl5_12 | ~spl5_20 | ~spl5_21 | ~spl5_26),
% 0.21/0.58    inference(avatar_split_clause,[],[f482,f364,f324,f313,f253,f166,f618])).
% 0.21/0.58  fof(f571,plain,(
% 0.21/0.58    spl5_34 | ~spl5_6 | ~spl5_12 | ~spl5_17 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26),
% 0.21/0.58    inference(avatar_split_clause,[],[f515,f364,f324,f313,f288,f283,f253,f166,f568])).
% 0.21/0.58  fof(f283,plain,(
% 0.21/0.58    spl5_17 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.58  fof(f515,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_6 | ~spl5_12 | ~spl5_17 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(forward_demodulation,[],[f486,f499])).
% 0.21/0.58  fof(f486,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl5_6 | ~spl5_12 | ~spl5_17 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f285,f481])).
% 0.21/0.58  fof(f285,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl5_17),
% 0.21/0.58    inference(avatar_component_clause,[],[f283])).
% 0.21/0.58  fof(f555,plain,(
% 0.21/0.58    ~spl5_31 | ~spl5_6 | spl5_10 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26),
% 0.21/0.58    inference(avatar_split_clause,[],[f505,f364,f324,f313,f288,f253,f221,f166,f552])).
% 0.21/0.58  fof(f221,plain,(
% 0.21/0.58    spl5_10 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.58  fof(f505,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl5_6 | spl5_10 | ~spl5_12 | ~spl5_18 | ~spl5_20 | ~spl5_21 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f223,f499])).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f221])).
% 0.21/0.58  fof(f480,plain,(
% 0.21/0.58    ~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16 | ~spl5_21 | ~spl5_25),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f479])).
% 0.21/0.58  fof(f479,plain,(
% 0.21/0.58    $false | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16 | ~spl5_21 | ~spl5_25)),
% 0.21/0.58    inference(global_subsumption,[],[f197,f228,f381,f380])).
% 0.21/0.58  fof(f380,plain,(
% 0.21/0.58    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16 | ~spl5_25)),
% 0.21/0.58    inference(backward_demodulation,[],[f305,f372])).
% 0.21/0.58  fof(f372,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | (~spl5_4 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f370,f159])).
% 0.21/0.58  fof(f370,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_25),
% 0.21/0.58    inference(superposition,[],[f362,f110])).
% 0.21/0.58  fof(f362,plain,(
% 0.21/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f360])).
% 0.21/0.58  fof(f305,plain,(
% 0.21/0.58    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f242,f302])).
% 0.21/0.58  fof(f302,plain,(
% 0.21/0.58    v1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_6 | ~spl5_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f301,f167])).
% 0.21/0.58  fof(f301,plain,(
% 0.21/0.58    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f300,f129])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f127])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_16),
% 0.21/0.58    inference(superposition,[],[f88,f277])).
% 0.21/0.58  fof(f277,plain,(
% 0.21/0.58    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl5_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f275])).
% 0.21/0.58  fof(f275,plain,(
% 0.21/0.58    spl5_16 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.58  fof(f242,plain,(
% 0.21/0.58    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f241,f210])).
% 0.21/0.58  fof(f210,plain,(
% 0.21/0.58    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f193,f205])).
% 0.21/0.58  fof(f205,plain,(
% 0.21/0.58    sK1 = k2_relat_1(sK2) | (~spl5_4 | ~spl5_7)),
% 0.21/0.58    inference(subsumption_resolution,[],[f203,f159])).
% 0.21/0.58  fof(f203,plain,(
% 0.21/0.58    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.21/0.58    inference(superposition,[],[f173,f109])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f171])).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    spl5_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.58  fof(f193,plain,(
% 0.21/0.58    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(backward_demodulation,[],[f189,f188])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f145,f167])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl5_1 | ~spl5_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f139,f134])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    v2_funct_1(sK2) | ~spl5_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f132])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    spl5_2 <=> v2_funct_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.58  fof(f139,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.58  fof(f189,plain,(
% 0.21/0.58    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f146,f167])).
% 0.21/0.58  fof(f146,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f140,f134])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f91])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.58  fof(f241,plain,(
% 0.21/0.58    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f232,f194])).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(backward_demodulation,[],[f190,f188])).
% 0.21/0.58  fof(f190,plain,(
% 0.21/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f147,f167])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f141,f134])).
% 0.21/0.58  fof(f141,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f232,plain,(
% 0.21/0.58    ~v1_relat_1(k4_relat_1(sK2)) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~spl5_11),
% 0.21/0.58    inference(resolution,[],[f228,f86])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.58  fof(f381,plain,(
% 0.21/0.58    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16 | ~spl5_25)),
% 0.21/0.58    inference(backward_demodulation,[],[f306,f372])).
% 0.21/0.58  fof(f306,plain,(
% 0.21/0.58    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11 | ~spl5_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f244,f302])).
% 0.21/0.58  fof(f244,plain,(
% 0.21/0.58    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f243,f210])).
% 0.21/0.58  fof(f243,plain,(
% 0.21/0.58    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f233,f194])).
% 0.21/0.58  fof(f233,plain,(
% 0.21/0.58    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) | ~spl5_11),
% 0.21/0.58    inference(resolution,[],[f228,f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f228,plain,(
% 0.21/0.58    v1_funct_1(k4_relat_1(sK2)) | ~spl5_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f226])).
% 0.21/0.58  fof(f226,plain,(
% 0.21/0.58    spl5_11 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(forward_demodulation,[],[f196,f188])).
% 0.21/0.58  fof(f196,plain,(
% 0.21/0.58    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(forward_demodulation,[],[f192,f188])).
% 0.21/0.58  fof(f192,plain,(
% 0.21/0.58    ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.21/0.58    inference(backward_demodulation,[],[f65,f188])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f29])).
% 0.21/0.58  fof(f29,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.58  fof(f453,plain,(
% 0.21/0.58    spl5_27 | ~spl5_3 | ~spl5_26),
% 0.21/0.58    inference(avatar_split_clause,[],[f397,f364,f150,f450])).
% 0.21/0.58  fof(f150,plain,(
% 0.21/0.58    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.58  fof(f397,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl5_3 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f152,f366])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,sK1) | ~spl5_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f150])).
% 0.21/0.58  fof(f435,plain,(
% 0.21/0.58    spl5_15 | ~spl5_26),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.58  fof(f434,plain,(
% 0.21/0.58    $false | (spl5_15 | ~spl5_26)),
% 0.21/0.58    inference(subsumption_resolution,[],[f405,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.58  fof(f405,plain,(
% 0.21/0.58    ~v1_xboole_0(k1_xboole_0) | (spl5_15 | ~spl5_26)),
% 0.21/0.58    inference(backward_demodulation,[],[f271,f366])).
% 0.21/0.58  fof(f271,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1) | spl5_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f270])).
% 0.21/0.58  fof(f270,plain,(
% 0.21/0.58    spl5_15 <=> v1_xboole_0(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.58  fof(f367,plain,(
% 0.21/0.58    spl5_25 | spl5_26 | ~spl5_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f155,f150,f364,f360])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_3),
% 0.21/0.58    inference(subsumption_resolution,[],[f154,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.21/0.58    inference(resolution,[],[f152,f118])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f64])).
% 0.21/0.58  fof(f355,plain,(
% 0.21/0.58    ~spl5_15 | ~spl5_18 | ~spl5_20 | spl5_23),
% 0.21/0.58    inference(avatar_split_clause,[],[f351,f338,f313,f288,f270])).
% 0.21/0.58  fof(f351,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1) | (~spl5_18 | ~spl5_20 | spl5_23)),
% 0.21/0.58    inference(forward_demodulation,[],[f350,f290])).
% 0.21/0.58  fof(f350,plain,(
% 0.21/0.58    ~v1_xboole_0(k1_relat_1(k4_relat_1(sK2))) | (~spl5_20 | spl5_23)),
% 0.21/0.58    inference(subsumption_resolution,[],[f349,f315])).
% 0.21/0.58  fof(f349,plain,(
% 0.21/0.58    ~v1_relat_1(k4_relat_1(sK2)) | ~v1_xboole_0(k1_relat_1(k4_relat_1(sK2))) | spl5_23),
% 0.21/0.58    inference(resolution,[],[f340,f84])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.58  fof(f340,plain,(
% 0.21/0.58    ~v1_xboole_0(k4_relat_1(sK2)) | spl5_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f338])).
% 0.21/0.58  fof(f346,plain,(
% 0.21/0.58    spl5_24 | ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f207,f171,f166,f157,f127,f343])).
% 0.21/0.58  fof(f207,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f185,f205])).
% 0.21/0.58  fof(f185,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl5_1 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f137,f167])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f87])).
% 0.21/0.58  fof(f327,plain,(
% 0.21/0.58    spl5_21 | ~spl5_1 | ~spl5_2 | ~spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f194,f166,f132,f127,f324])).
% 0.21/0.58  fof(f316,plain,(
% 0.21/0.58    spl5_20 | ~spl5_1 | ~spl5_6 | ~spl5_16),
% 0.21/0.58    inference(avatar_split_clause,[],[f302,f275,f166,f127,f313])).
% 0.21/0.58  fof(f291,plain,(
% 0.21/0.58    spl5_18 | ~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f210,f171,f166,f157,f132,f127,f288])).
% 0.21/0.58  fof(f286,plain,(
% 0.21/0.58    spl5_17 | ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f206,f171,f166,f157,f127,f283])).
% 0.21/0.58  fof(f206,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f184,f205])).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl5_1 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f136,f167])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f86])).
% 0.21/0.58  fof(f278,plain,(
% 0.21/0.58    spl5_16 | ~spl5_1 | ~spl5_2 | ~spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f188,f166,f132,f127,f275])).
% 0.21/0.58  fof(f256,plain,(
% 0.21/0.58    spl5_12 | ~spl5_4 | ~spl5_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f205,f171,f157,f253])).
% 0.21/0.58  fof(f229,plain,(
% 0.21/0.58    spl5_11 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f198,f166,f162,f132,f127,f226])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    spl5_5 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.58  fof(f198,plain,(
% 0.21/0.58    v1_funct_1(k4_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6)),
% 0.21/0.58    inference(forward_demodulation,[],[f164,f188])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    v1_funct_1(k2_funct_1(sK2)) | ~spl5_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f162])).
% 0.21/0.58  fof(f224,plain,(
% 0.21/0.58    ~spl5_9 | ~spl5_10 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f199,f166,f162,f132,f127,f221,f217])).
% 0.21/0.58  fof(f199,plain,(
% 0.21/0.58    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f197,f198])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ~spl5_4 | spl5_6),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    $false | (~spl5_4 | spl5_6)),
% 0.21/0.58    inference(subsumption_resolution,[],[f159,f178])).
% 0.21/0.58  fof(f178,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_6),
% 0.21/0.58    inference(resolution,[],[f168,f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.58  fof(f168,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | spl5_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f166])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    spl5_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f70,f171])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    spl5_5 | ~spl5_6 | ~spl5_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f138,f127,f166,f162])).
% 0.21/0.58  fof(f138,plain,(
% 0.21/0.58    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.21/0.58    inference(resolution,[],[f129,f89])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f46])).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    spl5_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f68,f157])).
% 0.21/0.58  fof(f153,plain,(
% 0.21/0.58    spl5_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f67,f150])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    spl5_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f69,f132])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    v2_funct_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f130,plain,(
% 0.21/0.58    spl5_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f66,f127])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    v1_funct_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (18367)------------------------------
% 0.21/0.58  % (18367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (18367)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (18367)Memory used [KB]: 11641
% 0.21/0.58  % (18367)Time elapsed: 0.184 s
% 0.21/0.58  % (18367)------------------------------
% 0.21/0.58  % (18367)------------------------------
% 0.21/0.58  % (18341)Success in time 0.226 s
%------------------------------------------------------------------------------
