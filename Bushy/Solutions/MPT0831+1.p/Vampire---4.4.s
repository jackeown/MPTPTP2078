%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t34_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:09 EDT 2019

% Result     : Theorem 3.85s
% Output     : Refutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  267 ( 502 expanded)
%              Number of leaves         :   64 ( 210 expanded)
%              Depth                    :   13
%              Number of atoms          :  838 (1507 expanded)
%              Number of equality atoms :   77 ( 142 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f132,f145,f153,f178,f185,f189,f212,f217,f248,f261,f296,f336,f462,f694,f780,f1124,f1865,f2519,f2602,f2623,f3398,f4079,f4193,f4230,f4256,f6061,f6077,f6087,f9336,f9350,f9613,f9643,f9744,f14076,f24957,f56593,f56726,f58316,f58365,f58436,f59278])).

fof(f59278,plain,
    ( ~ spl11_38
    | ~ spl11_428
    | spl11_435
    | ~ spl11_440
    | ~ spl11_2526 ),
    inference(avatar_contradiction_clause,[],[f59277])).

fof(f59277,plain,
    ( $false
    | ~ spl11_38
    | ~ spl11_428
    | ~ spl11_435
    | ~ spl11_440
    | ~ spl11_2526 ),
    inference(subsumption_resolution,[],[f59262,f4255])).

fof(f4255,plain,
    ( r2_relset_1(o_0_0_xboole_0,sK0,sK3,sK3)
    | ~ spl11_440 ),
    inference(avatar_component_clause,[],[f4254])).

fof(f4254,plain,
    ( spl11_440
  <=> r2_relset_1(o_0_0_xboole_0,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_440])])).

fof(f59262,plain,
    ( ~ r2_relset_1(o_0_0_xboole_0,sK0,sK3,sK3)
    | ~ spl11_38
    | ~ spl11_428
    | ~ spl11_435
    | ~ spl11_2526 ),
    inference(backward_demodulation,[],[f58971,f4229])).

fof(f4229,plain,
    ( ~ r2_relset_1(o_0_0_xboole_0,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ spl11_435 ),
    inference(avatar_component_clause,[],[f4228])).

fof(f4228,plain,
    ( spl11_435
  <=> ~ r2_relset_1(o_0_0_xboole_0,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_435])])).

fof(f58971,plain,
    ( ! [X1] : k7_relat_1(sK3,X1) = sK3
    | ~ spl11_38
    | ~ spl11_428
    | ~ spl11_2526 ),
    inference(subsumption_resolution,[],[f58867,f295])).

fof(f295,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl11_38
  <=> ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f58867,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK3,X1,sK3),o_0_0_xboole_0)
        | k7_relat_1(sK3,X1) = sK3 )
    | ~ spl11_428
    | ~ spl11_2526 ),
    inference(backward_demodulation,[],[f4192,f56725])).

fof(f56725,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK3,X1,sK3),sK1)
        | k7_relat_1(sK3,X1) = sK3 )
    | ~ spl11_2526 ),
    inference(avatar_component_clause,[],[f56724])).

fof(f56724,plain,
    ( spl11_2526
  <=> ! [X1] :
        ( k7_relat_1(sK3,X1) = sK3
        | r2_hidden(sK6(sK3,X1,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2526])])).

fof(f4192,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl11_428 ),
    inference(avatar_component_clause,[],[f4191])).

fof(f4191,plain,
    ( spl11_428
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_428])])).

fof(f58436,plain,
    ( ~ spl11_20
    | spl11_29
    | spl11_81
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(avatar_contradiction_clause,[],[f58435])).

fof(f58435,plain,
    ( $false
    | ~ spl11_20
    | ~ spl11_29
    | ~ spl11_81
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(subsumption_resolution,[],[f58425,f211])).

fof(f211,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl11_20
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f58425,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl11_29
    | ~ spl11_81
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(backward_demodulation,[],[f58417,f247])).

fof(f247,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl11_29
  <=> ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f58417,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | ~ spl11_81
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(subsumption_resolution,[],[f58416,f552])).

fof(f552,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl11_81 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl11_81
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f58416,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | v1_xboole_0(sK2)
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(duplicate_literal_removal,[],[f58411])).

fof(f58411,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | v1_xboole_0(sK2)
    | k7_relat_1(sK3,sK2) = sK3
    | ~ spl11_340
    | ~ spl11_2558 ),
    inference(resolution,[],[f58364,f3351])).

fof(f3351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK3,X0,sK3),X0)
        | v1_xboole_0(X0)
        | k7_relat_1(sK3,X0) = sK3 )
    | ~ spl11_340 ),
    inference(avatar_component_clause,[],[f3350])).

fof(f3350,plain,
    ( spl11_340
  <=> ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(sK3,X0,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_340])])).

fof(f58364,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK3,X0,sK3),sK2)
        | k7_relat_1(sK3,X0) = sK3 )
    | ~ spl11_2558 ),
    inference(avatar_component_clause,[],[f58363])).

fof(f58363,plain,
    ( spl11_2558
  <=> ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | m1_subset_1(sK6(sK3,X0,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2558])])).

fof(f58365,plain,
    ( spl11_2558
    | ~ spl11_58
    | ~ spl11_2556 ),
    inference(avatar_split_clause,[],[f58324,f58314,f454,f58363])).

fof(f454,plain,
    ( spl11_58
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | m1_subset_1(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f58314,plain,
    ( spl11_2556
  <=> ! [X2] :
        ( k7_relat_1(sK3,X2) = sK3
        | m1_subset_1(sK6(sK3,X2,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2556])])).

fof(f58324,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | m1_subset_1(sK6(sK3,X0,sK3),sK2) )
    | ~ spl11_58
    | ~ spl11_2556 ),
    inference(resolution,[],[f58315,f455])).

fof(f455,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | m1_subset_1(X3,sK2) )
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f454])).

fof(f58315,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(sK3,X2,sK3),sK1)
        | k7_relat_1(sK3,X2) = sK3 )
    | ~ spl11_2556 ),
    inference(avatar_component_clause,[],[f58314])).

fof(f58316,plain,
    ( spl11_2556
    | ~ spl11_2526 ),
    inference(avatar_split_clause,[],[f56753,f56724,f58314])).

fof(f56753,plain,
    ( ! [X2] :
        ( k7_relat_1(sK3,X2) = sK3
        | m1_subset_1(sK6(sK3,X2,sK3),sK1) )
    | ~ spl11_2526 ),
    inference(resolution,[],[f56725,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t1_subset)).

fof(f56726,plain,
    ( spl11_2526
    | spl11_125
    | ~ spl11_2436 ),
    inference(avatar_split_clause,[],[f56683,f55715,f970,f56724])).

fof(f970,plain,
    ( spl11_125
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f55715,plain,
    ( spl11_2436
  <=> ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | m1_subset_1(k4_tarski(sK6(sK3,X0,sK3),sK7(sK3,X0,sK3)),k2_zfmisc_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2436])])).

fof(f56683,plain,
    ( ! [X1] :
        ( k7_relat_1(sK3,X1) = sK3
        | r2_hidden(sK6(sK3,X1,sK3),sK1) )
    | ~ spl11_125
    | ~ spl11_2436 ),
    inference(subsumption_resolution,[],[f56678,f971])).

fof(f971,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl11_125 ),
    inference(avatar_component_clause,[],[f970])).

fof(f56678,plain,
    ( ! [X1] :
        ( k7_relat_1(sK3,X1) = sK3
        | v1_xboole_0(k2_zfmisc_1(sK1,sK0))
        | r2_hidden(sK6(sK3,X1,sK3),sK1) )
    | ~ spl11_2436 ),
    inference(resolution,[],[f55716,f193])).

fof(f193,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_zfmisc_1(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f103,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t2_subset)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t106_zfmisc_1)).

fof(f55716,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_tarski(sK6(sK3,X0,sK3),sK7(sK3,X0,sK3)),k2_zfmisc_1(sK1,sK0))
        | k7_relat_1(sK3,X0) = sK3 )
    | ~ spl11_2436 ),
    inference(avatar_component_clause,[],[f55715])).

fof(f56593,plain,
    ( spl11_2436
    | ~ spl11_8
    | ~ spl11_1294 ),
    inference(avatar_split_clause,[],[f38462,f24808,f151,f55715])).

fof(f151,plain,
    ( spl11_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f24808,plain,
    ( spl11_1294
  <=> ! [X7,X8] :
        ( k7_relat_1(sK3,X7) = sK3
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X8))
        | m1_subset_1(k4_tarski(sK6(sK3,X7,sK3),sK7(sK3,X7,sK3)),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1294])])).

fof(f38462,plain,
    ( ! [X1] :
        ( k7_relat_1(sK3,X1) = sK3
        | m1_subset_1(k4_tarski(sK6(sK3,X1,sK3),sK7(sK3,X1,sK3)),k2_zfmisc_1(sK1,sK0)) )
    | ~ spl11_8
    | ~ spl11_1294 ),
    inference(resolution,[],[f152,f24809])).

fof(f24809,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X8))
        | k7_relat_1(sK3,X7) = sK3
        | m1_subset_1(k4_tarski(sK6(sK3,X7,sK3),sK7(sK3,X7,sK3)),X8) )
    | ~ spl11_1294 ),
    inference(avatar_component_clause,[],[f24808])).

fof(f152,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f24957,plain,
    ( spl11_1294
    | ~ spl11_142 ),
    inference(avatar_split_clause,[],[f21677,f1119,f24808])).

fof(f1119,plain,
    ( spl11_142
  <=> ! [X17] :
        ( r2_hidden(k4_tarski(sK6(sK3,X17,sK3),sK7(sK3,X17,sK3)),sK3)
        | k7_relat_1(sK3,X17) = sK3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).

fof(f21677,plain,
    ( ! [X339,X338] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X338))
        | m1_subset_1(k4_tarski(sK6(sK3,X339,sK3),sK7(sK3,X339,sK3)),X338)
        | k7_relat_1(sK3,X339) = sK3 )
    | ~ spl11_142 ),
    inference(resolution,[],[f95,f1120])).

fof(f1120,plain,
    ( ! [X17] :
        ( r2_hidden(k4_tarski(sK6(sK3,X17,sK3),sK7(sK3,X17,sK3)),sK3)
        | k7_relat_1(sK3,X17) = sK3 )
    | ~ spl11_142 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t4_subset)).

fof(f14076,plain,
    ( ~ spl11_8
    | ~ spl11_124
    | spl11_711 ),
    inference(avatar_contradiction_clause,[],[f14070])).

fof(f14070,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_124
    | ~ spl11_711 ),
    inference(unit_resulting_resolution,[],[f9271,f152,f974,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f112_D])).

fof(f112_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f974,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl11_124 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl11_124
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_124])])).

fof(f9271,plain,
    ( ~ sP9(sK3)
    | ~ spl11_711 ),
    inference(avatar_component_clause,[],[f9270])).

fof(f9270,plain,
    ( spl11_711
  <=> ~ sP9(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_711])])).

fof(f9744,plain,
    ( ~ spl11_38
    | ~ spl11_112
    | ~ spl11_142
    | spl11_723
    | ~ spl11_728 ),
    inference(avatar_contradiction_clause,[],[f9743])).

fof(f9743,plain,
    ( $false
    | ~ spl11_38
    | ~ spl11_112
    | ~ spl11_142
    | ~ spl11_723
    | ~ spl11_728 ),
    inference(subsumption_resolution,[],[f9733,f9642])).

fof(f9642,plain,
    ( r2_relset_1(sK1,sK0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_728 ),
    inference(avatar_component_clause,[],[f9641])).

fof(f9641,plain,
    ( spl11_728
  <=> r2_relset_1(sK1,sK0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_728])])).

fof(f9733,plain,
    ( ~ r2_relset_1(sK1,sK0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_38
    | ~ spl11_112
    | ~ spl11_142
    | ~ spl11_723 ),
    inference(backward_demodulation,[],[f9571,f9612])).

fof(f9612,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl11_723 ),
    inference(avatar_component_clause,[],[f9611])).

fof(f9611,plain,
    ( spl11_723
  <=> ~ r2_relset_1(sK1,sK0,k7_relat_1(o_0_0_xboole_0,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_723])])).

fof(f9571,plain,
    ( ! [X17] : k7_relat_1(o_0_0_xboole_0,X17) = o_0_0_xboole_0
    | ~ spl11_38
    | ~ spl11_112
    | ~ spl11_142 ),
    inference(forward_demodulation,[],[f9570,f779])).

fof(f779,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl11_112 ),
    inference(avatar_component_clause,[],[f778])).

fof(f778,plain,
    ( spl11_112
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_112])])).

fof(f9570,plain,
    ( ! [X17] : k7_relat_1(sK3,X17) = sK3
    | ~ spl11_38
    | ~ spl11_112
    | ~ spl11_142 ),
    inference(subsumption_resolution,[],[f9515,f295])).

fof(f9515,plain,
    ( ! [X17] :
        ( r2_hidden(k4_tarski(sK6(o_0_0_xboole_0,X17,o_0_0_xboole_0),sK7(o_0_0_xboole_0,X17,o_0_0_xboole_0)),o_0_0_xboole_0)
        | k7_relat_1(sK3,X17) = sK3 )
    | ~ spl11_112
    | ~ spl11_142 ),
    inference(backward_demodulation,[],[f779,f1120])).

fof(f9643,plain,
    ( spl11_728
    | ~ spl11_20
    | ~ spl11_112 ),
    inference(avatar_split_clause,[],[f9490,f778,f210,f9641])).

fof(f9490,plain,
    ( r2_relset_1(sK1,sK0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_20
    | ~ spl11_112 ),
    inference(backward_demodulation,[],[f779,f211])).

fof(f9613,plain,
    ( ~ spl11_723
    | spl11_29
    | ~ spl11_112 ),
    inference(avatar_split_clause,[],[f9492,f778,f246,f9611])).

fof(f9492,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl11_29
    | ~ spl11_112 ),
    inference(backward_demodulation,[],[f779,f247])).

fof(f9350,plain,
    ( spl11_53
    | ~ spl11_244
    | ~ spl11_714 ),
    inference(avatar_contradiction_clause,[],[f9349])).

fof(f9349,plain,
    ( $false
    | ~ spl11_53
    | ~ spl11_244
    | ~ spl11_714 ),
    inference(subsumption_resolution,[],[f9343,f424])).

fof(f424,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl11_53
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f9343,plain,
    ( v1_xboole_0(sK3)
    | ~ spl11_244
    | ~ spl11_714 ),
    inference(resolution,[],[f9335,f2518])).

fof(f2518,plain,
    ( ! [X2] :
        ( r2_hidden(sK8(X2),X2)
        | v1_xboole_0(X2) )
    | ~ spl11_244 ),
    inference(avatar_component_clause,[],[f2517])).

fof(f2517,plain,
    ( spl11_244
  <=> ! [X2] :
        ( v1_xboole_0(X2)
        | r2_hidden(sK8(X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_244])])).

fof(f9335,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl11_714 ),
    inference(avatar_component_clause,[],[f9334])).

fof(f9334,plain,
    ( spl11_714
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_714])])).

fof(f9336,plain,
    ( spl11_714
    | ~ spl11_710 ),
    inference(avatar_split_clause,[],[f9296,f9273,f9334])).

fof(f9273,plain,
    ( spl11_710
  <=> sP9(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_710])])).

fof(f9296,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl11_710 ),
    inference(resolution,[],[f9274,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ sP9(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f96,f112_D])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t5_subset)).

fof(f9274,plain,
    ( sP9(sK3)
    | ~ spl11_710 ),
    inference(avatar_component_clause,[],[f9273])).

fof(f6087,plain,
    ( spl11_61
    | ~ spl11_608 ),
    inference(avatar_contradiction_clause,[],[f6081])).

fof(f6081,plain,
    ( $false
    | ~ spl11_61
    | ~ spl11_608 ),
    inference(unit_resulting_resolution,[],[f85,f458,f6076,f89])).

fof(f6076,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl11_608 ),
    inference(avatar_component_clause,[],[f6075])).

fof(f6075,plain,
    ( spl11_608
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_608])])).

fof(f458,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl11_61
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f14,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',existence_m1_subset_1)).

fof(f6077,plain,
    ( spl11_608
    | ~ spl11_604 ),
    inference(avatar_split_clause,[],[f6062,f6059,f6075])).

fof(f6059,plain,
    ( spl11_604
  <=> sP9(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_604])])).

fof(f6062,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl11_604 ),
    inference(resolution,[],[f6060,f113])).

fof(f6060,plain,
    ( sP9(sK1)
    | ~ spl11_604 ),
    inference(avatar_component_clause,[],[f6059])).

fof(f6061,plain,
    ( spl11_604
    | ~ spl11_22
    | ~ spl11_420 ),
    inference(avatar_split_clause,[],[f6050,f4077,f215,f6059])).

fof(f215,plain,
    ( spl11_22
  <=> ! [X0] :
        ( sP9(X0)
        | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f4077,plain,
    ( spl11_420
  <=> r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_420])])).

fof(f6050,plain,
    ( sP9(sK1)
    | ~ spl11_22
    | ~ spl11_420 ),
    inference(resolution,[],[f4078,f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | sP9(X0) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f215])).

fof(f4078,plain,
    ( r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl11_420 ),
    inference(avatar_component_clause,[],[f4077])).

fof(f4256,plain,
    ( spl11_440
    | ~ spl11_6
    | ~ spl11_20
    | ~ spl11_60 ),
    inference(avatar_split_clause,[],[f4145,f460,f210,f143,f4254])).

fof(f143,plain,
    ( spl11_6
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f460,plain,
    ( spl11_60
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f4145,plain,
    ( r2_relset_1(o_0_0_xboole_0,sK0,sK3,sK3)
    | ~ spl11_6
    | ~ spl11_20
    | ~ spl11_60 ),
    inference(backward_demodulation,[],[f4141,f211])).

fof(f4141,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl11_6
    | ~ spl11_60 ),
    inference(resolution,[],[f461,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f461,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f460])).

fof(f4230,plain,
    ( ~ spl11_435
    | ~ spl11_6
    | spl11_29
    | ~ spl11_60 ),
    inference(avatar_split_clause,[],[f4147,f460,f246,f143,f4228])).

fof(f4147,plain,
    ( ~ r2_relset_1(o_0_0_xboole_0,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ spl11_6
    | ~ spl11_29
    | ~ spl11_60 ),
    inference(backward_demodulation,[],[f4141,f247])).

fof(f4193,plain,
    ( spl11_428
    | ~ spl11_6
    | ~ spl11_60 ),
    inference(avatar_split_clause,[],[f4141,f460,f143,f4191])).

fof(f4079,plain,
    ( spl11_420
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_80 ),
    inference(avatar_split_clause,[],[f4061,f554,f143,f130,f4077])).

fof(f130,plain,
    ( spl11_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f554,plain,
    ( spl11_80
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f4061,plain,
    ( r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_80 ),
    inference(backward_demodulation,[],[f4038,f131])).

fof(f131,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f4038,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl11_6
    | ~ spl11_80 ),
    inference(resolution,[],[f555,f144])).

fof(f555,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_80 ),
    inference(avatar_component_clause,[],[f554])).

fof(f3398,plain,
    ( spl11_340
    | ~ spl11_12
    | ~ spl11_142 ),
    inference(avatar_split_clause,[],[f2515,f1119,f176,f3350])).

fof(f176,plain,
    ( spl11_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f2515,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(sK3,X0,sK3),X0) )
    | ~ spl11_12
    | ~ spl11_142 ),
    inference(subsumption_resolution,[],[f2514,f1120])).

fof(f2514,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | ~ r2_hidden(k4_tarski(sK6(sK3,X0,sK3),sK7(sK3,X0,sK3)),sK3)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(sK3,X0,sK3),X0) )
    | ~ spl11_12
    | ~ spl11_142 ),
    inference(subsumption_resolution,[],[f2513,f177])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f2513,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | ~ r2_hidden(k4_tarski(sK6(sK3,X0,sK3),sK7(sK3,X0,sK3)),sK3)
        | ~ v1_relat_1(sK3)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(sK3,X0,sK3),X0) )
    | ~ spl11_142 ),
    inference(duplicate_literal_removal,[],[f2511])).

fof(f2511,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = sK3
        | ~ r2_hidden(k4_tarski(sK6(sK3,X0,sK3),sK7(sK3,X0,sK3)),sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK3)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(sK3,X0,sK3),X0)
        | k7_relat_1(sK3,X0) = sK3 )
    | ~ spl11_142 ),
    inference(resolution,[],[f302,f1120])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK6(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f84,f89])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',d11_relat_1)).

fof(f2623,plain,
    ( spl11_24
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f2603,f198,f226])).

fof(f226,plain,
    ( spl11_24
  <=> ! [X0] : ~ r2_hidden(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f198,plain,
    ( spl11_18
  <=> sP9(sK8(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f2603,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_18 ),
    inference(resolution,[],[f199,f113])).

fof(f199,plain,
    ( sP9(sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f2602,plain,
    ( spl11_18
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f2600,f187,f198])).

fof(f187,plain,
    ( spl11_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP9(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f2600,plain,
    ( sP9(sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_16 ),
    inference(resolution,[],[f188,f85])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP9(X0) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f2519,plain,
    ( spl11_244
    | spl11_182 ),
    inference(avatar_split_clause,[],[f1104,f1698,f2517])).

fof(f1698,plain,
    ( spl11_182
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_182])])).

fof(f1104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | r2_hidden(sK8(X2),X2) ) ),
    inference(resolution,[],[f590,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f590,plain,(
    ! [X28,X26,X27] :
      ( r2_hidden(k4_tarski(X27,sK8(X28)),k2_zfmisc_1(X26,X28))
      | ~ m1_subset_1(X27,X26)
      | v1_xboole_0(X28)
      | v1_xboole_0(X26) ) ),
    inference(resolution,[],[f361,f85])).

fof(f361,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X3)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f213,f89])).

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f105,f89])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1865,plain,
    ( spl11_53
    | ~ spl11_182 ),
    inference(avatar_contradiction_clause,[],[f1839])).

fof(f1839,plain,
    ( $false
    | ~ spl11_53
    | ~ spl11_182 ),
    inference(unit_resulting_resolution,[],[f424,f85,f1699])).

fof(f1699,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl11_182 ),
    inference(avatar_component_clause,[],[f1698])).

fof(f1124,plain,
    ( spl11_142
    | ~ spl11_12
    | ~ spl11_100 ),
    inference(avatar_split_clause,[],[f900,f692,f176,f1119])).

fof(f692,plain,
    ( spl11_100
  <=> ! [X5,X4] :
        ( r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),sK3)
        | r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),X5)
        | ~ v1_relat_1(X5)
        | k7_relat_1(sK3,X4) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f900,plain,
    ( ! [X17] :
        ( r2_hidden(k4_tarski(sK6(sK3,X17,sK3),sK7(sK3,X17,sK3)),sK3)
        | k7_relat_1(sK3,X17) = sK3 )
    | ~ spl11_12
    | ~ spl11_100 ),
    inference(duplicate_literal_removal,[],[f898])).

fof(f898,plain,
    ( ! [X17] :
        ( r2_hidden(k4_tarski(sK6(sK3,X17,sK3),sK7(sK3,X17,sK3)),sK3)
        | r2_hidden(k4_tarski(sK6(sK3,X17,sK3),sK7(sK3,X17,sK3)),sK3)
        | k7_relat_1(sK3,X17) = sK3 )
    | ~ spl11_12
    | ~ spl11_100 ),
    inference(resolution,[],[f693,f177])).

fof(f693,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),X5)
        | r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),sK3)
        | k7_relat_1(sK3,X4) = X5 )
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f692])).

fof(f780,plain,
    ( spl11_112
    | ~ spl11_6
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f750,f426,f143,f778])).

fof(f426,plain,
    ( spl11_52
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f750,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl11_6
    | ~ spl11_52 ),
    inference(resolution,[],[f427,f144])).

fof(f427,plain,
    ( v1_xboole_0(sK3)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f426])).

fof(f694,plain,
    ( spl11_100
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f299,f176,f692])).

fof(f299,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),sK3)
        | r2_hidden(k4_tarski(sK6(sK3,X4,X5),sK7(sK3,X4,X5)),X5)
        | ~ v1_relat_1(X5)
        | k7_relat_1(sK3,X4) = X5 )
    | ~ spl11_12 ),
    inference(resolution,[],[f83,f177])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f462,plain,
    ( spl11_58
    | spl11_60
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f450,f130,f460,f454])).

fof(f450,plain,
    ( ! [X3] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X3,sK1)
        | m1_subset_1(X3,sK2) )
    | ~ spl11_2 ),
    inference(resolution,[],[f325,f131])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f190,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t3_subset)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f95,f89])).

fof(f336,plain,(
    ~ spl11_30 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl11_30 ),
    inference(unit_resulting_resolution,[],[f85,f254])).

fof(f254,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl11_30
  <=> ! [X0] : ~ m1_subset_1(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f296,plain,
    ( spl11_38
    | ~ spl11_6
    | ~ spl11_24
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f269,f259,f226,f143,f294])).

fof(f259,plain,
    ( spl11_32
  <=> v1_xboole_0(sK8(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f269,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl11_6
    | ~ spl11_24
    | ~ spl11_32 ),
    inference(backward_demodulation,[],[f265,f227])).

fof(f227,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f265,plain,
    ( o_0_0_xboole_0 = sK8(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl11_6
    | ~ spl11_32 ),
    inference(resolution,[],[f260,f144])).

fof(f260,plain,
    ( v1_xboole_0(sK8(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl11_30
    | spl11_32
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f230,f226,f259,f253])).

fof(f230,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK8(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK8(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl11_24 ),
    inference(resolution,[],[f227,f89])).

fof(f248,plain,
    ( ~ spl11_29
    | ~ spl11_8
    | spl11_15 ),
    inference(avatar_split_clause,[],[f237,f183,f151,f246])).

fof(f183,plain,
    ( spl11_15
  <=> ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f237,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ spl11_8
    | ~ spl11_15 ),
    inference(backward_demodulation,[],[f219,f184])).

fof(f184,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f219,plain,
    ( ! [X3] : k5_relset_1(sK1,sK0,sK3,X3) = k7_relat_1(sK3,X3)
    | ~ spl11_8 ),
    inference(resolution,[],[f97,f152])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',redefinition_k5_relset_1)).

fof(f217,plain,
    ( spl11_22
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f192,f187,f215])).

fof(f192,plain,
    ( ! [X0] :
        ( sP9(X0)
        | ~ r1_tarski(X0,o_0_0_xboole_0) )
    | ~ spl11_16 ),
    inference(resolution,[],[f188,f91])).

fof(f212,plain,
    ( spl11_20
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f204,f151,f210])).

fof(f204,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl11_8 ),
    inference(resolution,[],[f116,f152])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',redefinition_r2_relset_1)).

fof(f189,plain,
    ( spl11_16
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f171,f123,f187])).

fof(f123,plain,
    ( spl11_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP9(X0) )
    | ~ spl11_0 ),
    inference(resolution,[],[f112,f124])).

fof(f124,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f185,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f72,f183])).

fof(f72,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t34_relset_1)).

fof(f178,plain,
    ( spl11_12
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f169,f151,f176])).

fof(f169,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_8 ),
    inference(resolution,[],[f94,f152])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',cc1_relset_1)).

fof(f153,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f70,f151])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f145,plain,
    ( spl11_6
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f134,f123,f143])).

fof(f134,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl11_0 ),
    inference(backward_demodulation,[],[f133,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',t6_boole)).

fof(f133,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_0 ),
    inference(resolution,[],[f74,f124])).

fof(f132,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f71,f130])).

fof(f71,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f73,f123])).

fof(f73,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t34_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
