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
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 509 expanded)
%              Number of leaves         :   49 ( 215 expanded)
%              Depth                    :   16
%              Number of atoms          : 1084 (2661 expanded)
%              Number of equality atoms :  240 ( 739 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f603,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f154,f164,f170,f193,f216,f223,f233,f251,f266,f282,f367,f401,f405,f422,f463,f487,f515,f530,f580,f602])).

fof(f602,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_26
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_26
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f600,f263])).

fof(f263,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl4_26
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f600,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f599,f378])).

fof(f378,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f599,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_52 ),
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f597,f190])).

% (23107)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f190,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f597,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f596,f169])).

fof(f169,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f596,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f595,f147])).

fof(f147,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f595,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f594,f163])).

fof(f163,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f594,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f593,f132])).

fof(f132,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

% (23111)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f130,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f593,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f592,f107])).

fof(f107,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f592,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f587,f92])).

fof(f92,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f587,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_52 ),
    inference(superposition,[],[f59,f579])).

fof(f579,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl4_52
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f580,plain,
    ( spl4_52
    | ~ spl4_39
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f575,f527,f396,f577])).

fof(f396,plain,
    ( spl4_39
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f527,plain,
    ( spl4_49
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f575,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_39
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f398,f529])).

fof(f529,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f527])).

fof(f398,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f396])).

fof(f530,plain,
    ( ~ spl4_24
    | spl4_49
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f525,f460,f376,f228,f188,f167,f161,f145,f130,f527,f245])).

fof(f245,plain,
    ( spl4_24
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f228,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f460,plain,
    ( spl4_46
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f525,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f524,f190])).

fof(f524,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f523,f230])).

fof(f230,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f228])).

% (23108)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f523,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(trivial_inequality_removal,[],[f522])).

fof(f522,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f521,f378])).

fof(f521,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f520,f163])).

fof(f520,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f519,f132])).

fof(f519,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f518,f169])).

fof(f518,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f513,f147])).

fof(f513,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f59,f462])).

fof(f462,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f460])).

fof(f515,plain,
    ( spl4_40
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | spl4_40
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f510,f69])).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f510,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl4_40
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f421,f462])).

fof(f421,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl4_40
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f487,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_45 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_45 ),
    inference(unit_resulting_resolution,[],[f147,f132,f137,f122,f458,f290])).

fof(f290,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

% (23101)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (23100)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f458,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl4_45
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f463,plain,
    ( ~ spl4_45
    | spl4_46
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f444,f279,f460,f456])).

fof(f279,plain,
    ( spl4_27
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f444,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_27 ),
    inference(resolution,[],[f254,f281])).

fof(f281,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f279])).

fof(f254,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f70,f155])).

fof(f155,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f73,f74])).

% (23103)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

% (23099)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f422,plain,
    ( ~ spl4_40
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f417,f249,f188,f167,f145,f419])).

fof(f249,plain,
    ( spl4_25
  <=> ! [X0] :
        ( k2_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f417,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f416,f147])).

fof(f416,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f415,f169])).

fof(f415,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(trivial_inequality_removal,[],[f413])).

fof(f413,plain,
    ( sK1 != sK1
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(superposition,[],[f250,f190])).

fof(f250,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK3)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f249])).

fof(f405,plain,
    ( spl4_39
    | ~ spl4_24
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f404,f364,f130,f125,f120,f100,f245,f396])).

fof(f100,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f125,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f364,plain,
    ( spl4_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f404,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f403,f132])).

fof(f403,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f402,f127])).

fof(f127,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f402,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f390,f122])).

fof(f390,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f372,f102])).

fof(f102,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f372,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f370])).

fof(f370,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f292,f366])).

fof(f366,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f364])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f57,f74])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f401,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f400,f364,f120,f376])).

fof(f400,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f371,f122])).

fof(f371,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_36 ),
    inference(superposition,[],[f78,f366])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f367,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f362,f151,f145,f140,f135,f130,f125,f120,f364])).

fof(f140,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f151,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f362,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f361,f132])).

fof(f361,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f360,f127])).

fof(f360,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f359,f122])).

fof(f359,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f358,f147])).

fof(f358,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f357,f142])).

fof(f142,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f357,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f354,f137])).

fof(f354,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f353,f153])).

fof(f153,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f353,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f72,f74])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f282,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f277,f151,f145,f135,f130,f120,f279])).

fof(f277,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f276,f147])).

fof(f276,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f275,f137])).

fof(f275,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f274,f132])).

fof(f274,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f271,f122])).

% (23100)Refutation not found, incomplete strategy% (23100)------------------------------
% (23100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f271,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f153,f77])).

% (23100)Termination reason: Refutation not found, incomplete strategy

% (23100)Memory used [KB]: 10746
% (23100)Time elapsed: 0.207 s
% (23100)------------------------------
% (23100)------------------------------
fof(f266,plain,
    ( spl4_26
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f265,f220,f135,f261])).

fof(f220,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f265,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f257,f137])).

fof(f257,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(superposition,[],[f81,f222])).

fof(f222,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f251,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f243,f228,f161,f130,f249,f245])).

fof(f243,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f242,f163])).

fof(f242,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f241,f132])).

fof(f241,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_23 ),
    inference(superposition,[],[f67,f230])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f233,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f232,f213,f120,f228])).

fof(f213,plain,
    ( spl4_21
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f232,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f225,f122])).

fof(f225,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(superposition,[],[f81,f215])).

fof(f215,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f213])).

fof(f223,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f218,f140,f135,f95,f220])).

fof(f95,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f218,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f217,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f217,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f208,f142])).

fof(f208,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f60,f137])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f216,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f211,f125,f120,f100,f213])).

fof(f211,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f210,f102])).

fof(f210,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f207,f127])).

fof(f207,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f60,f122])).

fof(f193,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f192,f135,f115,f188])).

fof(f115,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f192,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f185,f137])).

fof(f185,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f117,f78])).

fof(f117,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f170,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f165,f135,f167])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f157,f80])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f157,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f79,f137])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f164,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f159,f120,f161])).

fof(f159,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f156,f80])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f79,f122])).

fof(f154,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f149,f110,f151])).

fof(f110,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f149,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f112,f74])).

fof(f112,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f148,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f45,f145])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f143,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f46,f140])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f47,f135])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f48,f130])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f128,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f49,f125])).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f120])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f115])).

fof(f51,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f55,f95])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f56,f90])).

fof(f56,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.55  % (23089)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (23104)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (23096)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (23090)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (23087)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (23113)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (23105)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (23106)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (23112)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (23110)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (23097)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.58  % (23098)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.58  % (23102)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (23094)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.85/0.60  % (23112)Refutation not found, incomplete strategy% (23112)------------------------------
% 1.85/0.60  % (23112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (23112)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (23112)Memory used [KB]: 11001
% 1.85/0.60  % (23112)Time elapsed: 0.102 s
% 1.85/0.60  % (23112)------------------------------
% 1.85/0.60  % (23112)------------------------------
% 1.97/0.62  % (23105)Refutation found. Thanks to Tanya!
% 1.97/0.62  % SZS status Theorem for theBenchmark
% 1.97/0.62  % (23088)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.97/0.62  % (23086)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.97/0.62  % (23084)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.97/0.62  % (23085)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.97/0.63  % (23109)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.97/0.63  % SZS output start Proof for theBenchmark
% 1.97/0.63  fof(f603,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f154,f164,f170,f193,f216,f223,f233,f251,f266,f282,f367,f401,f405,f422,f463,f487,f515,f530,f580,f602])).
% 1.97/0.63  fof(f602,plain,(
% 1.97/0.63    spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_26 | ~spl4_37 | ~spl4_52),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f601])).
% 1.97/0.63  fof(f601,plain,(
% 1.97/0.63    $false | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_26 | ~spl4_37 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f600,f263])).
% 1.97/0.63  fof(f263,plain,(
% 1.97/0.63    sK0 = k1_relat_1(sK2) | ~spl4_26),
% 1.97/0.63    inference(avatar_component_clause,[],[f261])).
% 1.97/0.63  fof(f261,plain,(
% 1.97/0.63    spl4_26 <=> sK0 = k1_relat_1(sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.97/0.63  fof(f600,plain,(
% 1.97/0.63    sK0 != k1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_52)),
% 1.97/0.63    inference(forward_demodulation,[],[f599,f378])).
% 1.97/0.63  fof(f378,plain,(
% 1.97/0.63    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 1.97/0.63    inference(avatar_component_clause,[],[f376])).
% 1.97/0.63  fof(f376,plain,(
% 1.97/0.63    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.97/0.63  fof(f599,plain,(
% 1.97/0.63    k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_52)),
% 1.97/0.63    inference(trivial_inequality_removal,[],[f598])).
% 1.97/0.63  fof(f598,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_52)),
% 1.97/0.63    inference(forward_demodulation,[],[f597,f190])).
% 1.97/0.63  % (23107)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.97/0.63  fof(f190,plain,(
% 1.97/0.63    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.97/0.63    inference(avatar_component_clause,[],[f188])).
% 1.97/0.63  fof(f188,plain,(
% 1.97/0.63    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.97/0.63  fof(f597,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f596,f169])).
% 1.97/0.63  fof(f169,plain,(
% 1.97/0.63    v1_relat_1(sK2) | ~spl4_15),
% 1.97/0.63    inference(avatar_component_clause,[],[f167])).
% 1.97/0.63  fof(f167,plain,(
% 1.97/0.63    spl4_15 <=> v1_relat_1(sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.97/0.63  fof(f596,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f595,f147])).
% 1.97/0.63  fof(f147,plain,(
% 1.97/0.63    v1_funct_1(sK2) | ~spl4_12),
% 1.97/0.63    inference(avatar_component_clause,[],[f145])).
% 1.97/0.63  fof(f145,plain,(
% 1.97/0.63    spl4_12 <=> v1_funct_1(sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.97/0.63  fof(f595,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_14 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f594,f163])).
% 1.97/0.63  fof(f163,plain,(
% 1.97/0.63    v1_relat_1(sK3) | ~spl4_14),
% 1.97/0.63    inference(avatar_component_clause,[],[f161])).
% 1.97/0.63  fof(f161,plain,(
% 1.97/0.63    spl4_14 <=> v1_relat_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.97/0.63  fof(f594,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f593,f132])).
% 1.97/0.63  fof(f132,plain,(
% 1.97/0.63    v1_funct_1(sK3) | ~spl4_9),
% 1.97/0.63    inference(avatar_component_clause,[],[f130])).
% 1.97/0.63  % (23111)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.97/0.63  fof(f130,plain,(
% 1.97/0.63    spl4_9 <=> v1_funct_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.97/0.63  fof(f593,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f592,f107])).
% 1.97/0.63  fof(f107,plain,(
% 1.97/0.63    v2_funct_1(sK2) | ~spl4_4),
% 1.97/0.63    inference(avatar_component_clause,[],[f105])).
% 1.97/0.63  fof(f105,plain,(
% 1.97/0.63    spl4_4 <=> v2_funct_1(sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.97/0.63  fof(f592,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_52)),
% 1.97/0.63    inference(subsumption_resolution,[],[f587,f92])).
% 1.97/0.63  fof(f92,plain,(
% 1.97/0.63    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.97/0.63    inference(avatar_component_clause,[],[f90])).
% 1.97/0.63  fof(f90,plain,(
% 1.97/0.63    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.97/0.63  fof(f587,plain,(
% 1.97/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_52),
% 1.97/0.63    inference(superposition,[],[f59,f579])).
% 1.97/0.63  fof(f579,plain,(
% 1.97/0.63    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | ~spl4_52),
% 1.97/0.63    inference(avatar_component_clause,[],[f577])).
% 1.97/0.63  fof(f577,plain,(
% 1.97/0.63    spl4_52 <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.97/0.63  fof(f59,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f24])).
% 1.97/0.63  fof(f24,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.63    inference(flattening,[],[f23])).
% 1.97/0.63  fof(f23,plain,(
% 1.97/0.63    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f5])).
% 1.97/0.63  fof(f5,axiom,(
% 1.97/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.97/0.63  fof(f580,plain,(
% 1.97/0.63    spl4_52 | ~spl4_39 | ~spl4_49),
% 1.97/0.63    inference(avatar_split_clause,[],[f575,f527,f396,f577])).
% 1.97/0.63  fof(f396,plain,(
% 1.97/0.63    spl4_39 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.97/0.63  fof(f527,plain,(
% 1.97/0.63    spl4_49 <=> sK2 = k2_funct_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.97/0.63  fof(f575,plain,(
% 1.97/0.63    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_39 | ~spl4_49)),
% 1.97/0.63    inference(forward_demodulation,[],[f398,f529])).
% 1.97/0.63  fof(f529,plain,(
% 1.97/0.63    sK2 = k2_funct_1(sK3) | ~spl4_49),
% 1.97/0.63    inference(avatar_component_clause,[],[f527])).
% 1.97/0.63  fof(f398,plain,(
% 1.97/0.63    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_39),
% 1.97/0.63    inference(avatar_component_clause,[],[f396])).
% 1.97/0.63  fof(f530,plain,(
% 1.97/0.63    ~spl4_24 | spl4_49 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_37 | ~spl4_46),
% 1.97/0.63    inference(avatar_split_clause,[],[f525,f460,f376,f228,f188,f167,f161,f145,f130,f527,f245])).
% 1.97/0.63  fof(f245,plain,(
% 1.97/0.63    spl4_24 <=> v2_funct_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.97/0.63  fof(f228,plain,(
% 1.97/0.63    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.97/0.63  fof(f460,plain,(
% 1.97/0.63    spl4_46 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.97/0.63  fof(f525,plain,(
% 1.97/0.63    sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_37 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f524,f190])).
% 1.97/0.63  fof(f524,plain,(
% 1.97/0.63    sK1 != k2_relat_1(sK2) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_37 | ~spl4_46)),
% 1.97/0.63    inference(forward_demodulation,[],[f523,f230])).
% 1.97/0.63  fof(f230,plain,(
% 1.97/0.63    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 1.97/0.63    inference(avatar_component_clause,[],[f228])).
% 1.97/0.63  % (23108)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.97/0.63  fof(f523,plain,(
% 1.97/0.63    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_46)),
% 1.97/0.63    inference(trivial_inequality_removal,[],[f522])).
% 1.97/0.63  fof(f522,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_46)),
% 1.97/0.63    inference(forward_demodulation,[],[f521,f378])).
% 1.97/0.63  fof(f521,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f520,f163])).
% 1.97/0.63  fof(f520,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f519,f132])).
% 1.97/0.63  fof(f519,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f518,f169])).
% 1.97/0.63  fof(f518,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f513,f147])).
% 1.97/0.63  fof(f513,plain,(
% 1.97/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.97/0.63    inference(superposition,[],[f59,f462])).
% 1.97/0.63  fof(f462,plain,(
% 1.97/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_46),
% 1.97/0.63    inference(avatar_component_clause,[],[f460])).
% 1.97/0.63  fof(f515,plain,(
% 1.97/0.63    spl4_40 | ~spl4_46),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f514])).
% 1.97/0.63  fof(f514,plain,(
% 1.97/0.63    $false | (spl4_40 | ~spl4_46)),
% 1.97/0.63    inference(subsumption_resolution,[],[f510,f69])).
% 1.97/0.63  fof(f69,plain,(
% 1.97/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f3])).
% 1.97/0.63  fof(f3,axiom,(
% 1.97/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.97/0.63  fof(f510,plain,(
% 1.97/0.63    ~v2_funct_1(k6_relat_1(sK0)) | (spl4_40 | ~spl4_46)),
% 1.97/0.63    inference(backward_demodulation,[],[f421,f462])).
% 1.97/0.63  fof(f421,plain,(
% 1.97/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_40),
% 1.97/0.63    inference(avatar_component_clause,[],[f419])).
% 1.97/0.63  fof(f419,plain,(
% 1.97/0.63    spl4_40 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.97/0.63  fof(f487,plain,(
% 1.97/0.63    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_45),
% 1.97/0.63    inference(avatar_contradiction_clause,[],[f474])).
% 1.97/0.63  fof(f474,plain,(
% 1.97/0.63    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_45)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f147,f132,f137,f122,f458,f290])).
% 1.97/0.63  fof(f290,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.97/0.63    inference(duplicate_literal_removal,[],[f289])).
% 1.97/0.63  fof(f289,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.97/0.63    inference(superposition,[],[f76,f77])).
% 1.97/0.63  fof(f77,plain,(
% 1.97/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f36])).
% 2.09/0.63  % (23101)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.09/0.63  % (23100)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.09/0.63  fof(f36,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.09/0.63    inference(flattening,[],[f35])).
% 2.09/0.63  fof(f35,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.09/0.63    inference(ennf_transformation,[],[f12])).
% 2.09/0.63  fof(f12,axiom,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.09/0.63  fof(f76,plain,(
% 2.09/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f34])).
% 2.09/0.63  fof(f34,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.09/0.63    inference(flattening,[],[f33])).
% 2.09/0.63  fof(f33,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.09/0.63    inference(ennf_transformation,[],[f10])).
% 2.09/0.63  fof(f10,axiom,(
% 2.09/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.09/0.63  fof(f458,plain,(
% 2.09/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_45),
% 2.09/0.63    inference(avatar_component_clause,[],[f456])).
% 2.09/0.63  fof(f456,plain,(
% 2.09/0.63    spl4_45 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.09/0.63  fof(f122,plain,(
% 2.09/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.09/0.63    inference(avatar_component_clause,[],[f120])).
% 2.09/0.63  fof(f120,plain,(
% 2.09/0.63    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.09/0.63  fof(f137,plain,(
% 2.09/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.09/0.63    inference(avatar_component_clause,[],[f135])).
% 2.09/0.63  fof(f135,plain,(
% 2.09/0.63    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.09/0.63  fof(f463,plain,(
% 2.09/0.63    ~spl4_45 | spl4_46 | ~spl4_27),
% 2.09/0.63    inference(avatar_split_clause,[],[f444,f279,f460,f456])).
% 2.09/0.63  fof(f279,plain,(
% 2.09/0.63    spl4_27 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.09/0.63  fof(f444,plain,(
% 2.09/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_27),
% 2.09/0.63    inference(resolution,[],[f254,f281])).
% 2.09/0.63  fof(f281,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_27),
% 2.09/0.63    inference(avatar_component_clause,[],[f279])).
% 2.09/0.63  fof(f254,plain,(
% 2.09/0.63    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.09/0.63    inference(resolution,[],[f70,f155])).
% 2.09/0.63  fof(f155,plain,(
% 2.09/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.09/0.63    inference(forward_demodulation,[],[f73,f74])).
% 2.09/0.63  % (23103)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.09/0.63  fof(f74,plain,(
% 2.09/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f13])).
% 2.09/0.63  fof(f13,axiom,(
% 2.09/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.09/0.63  fof(f73,plain,(
% 2.09/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.09/0.63    inference(cnf_transformation,[],[f18])).
% 2.09/0.63  fof(f18,plain,(
% 2.09/0.63    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.09/0.63    inference(pure_predicate_removal,[],[f11])).
% 2.09/0.63  % (23099)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.09/0.63  fof(f11,axiom,(
% 2.09/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.09/0.63  fof(f70,plain,(
% 2.09/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.63    inference(cnf_transformation,[],[f44])).
% 2.09/0.63  fof(f44,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.63    inference(nnf_transformation,[],[f30])).
% 2.09/0.63  fof(f30,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.63    inference(flattening,[],[f29])).
% 2.09/0.63  fof(f29,plain,(
% 2.09/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.09/0.63    inference(ennf_transformation,[],[f8])).
% 2.09/0.63  fof(f8,axiom,(
% 2.09/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.09/0.63  fof(f422,plain,(
% 2.09/0.63    ~spl4_40 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_25),
% 2.09/0.63    inference(avatar_split_clause,[],[f417,f249,f188,f167,f145,f419])).
% 2.09/0.63  fof(f249,plain,(
% 2.09/0.63    spl4_25 <=> ! [X0] : (k2_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK3)))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.09/0.63  fof(f417,plain,(
% 2.09/0.63    ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_25)),
% 2.09/0.63    inference(subsumption_resolution,[],[f416,f147])).
% 2.09/0.63  fof(f416,plain,(
% 2.09/0.63    ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_15 | ~spl4_18 | ~spl4_25)),
% 2.09/0.63    inference(subsumption_resolution,[],[f415,f169])).
% 2.09/0.63  fof(f415,plain,(
% 2.09/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_18 | ~spl4_25)),
% 2.09/0.63    inference(trivial_inequality_removal,[],[f413])).
% 2.09/0.63  fof(f413,plain,(
% 2.09/0.63    sK1 != sK1 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_18 | ~spl4_25)),
% 2.09/0.63    inference(superposition,[],[f250,f190])).
% 2.09/0.63  fof(f250,plain,(
% 2.09/0.63    ( ! [X0] : (k2_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK3))) ) | ~spl4_25),
% 2.09/0.63    inference(avatar_component_clause,[],[f249])).
% 2.09/0.63  fof(f405,plain,(
% 2.09/0.63    spl4_39 | ~spl4_24 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 2.09/0.63    inference(avatar_split_clause,[],[f404,f364,f130,f125,f120,f100,f245,f396])).
% 2.09/0.63  fof(f100,plain,(
% 2.09/0.63    spl4_3 <=> k1_xboole_0 = sK0),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.09/0.63  fof(f125,plain,(
% 2.09/0.63    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.09/0.63  fof(f364,plain,(
% 2.09/0.63    spl4_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.09/0.63  fof(f404,plain,(
% 2.09/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 2.09/0.63    inference(subsumption_resolution,[],[f403,f132])).
% 2.09/0.63  fof(f403,plain,(
% 2.09/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 2.09/0.63    inference(subsumption_resolution,[],[f402,f127])).
% 2.09/0.63  fof(f127,plain,(
% 2.09/0.63    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.09/0.63    inference(avatar_component_clause,[],[f125])).
% 2.09/0.63  fof(f402,plain,(
% 2.09/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_36)),
% 2.09/0.63    inference(subsumption_resolution,[],[f390,f122])).
% 2.09/0.63  fof(f390,plain,(
% 2.09/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_36)),
% 2.09/0.63    inference(subsumption_resolution,[],[f372,f102])).
% 2.09/0.63  fof(f102,plain,(
% 2.09/0.63    k1_xboole_0 != sK0 | spl4_3),
% 2.09/0.63    inference(avatar_component_clause,[],[f100])).
% 2.09/0.63  fof(f372,plain,(
% 2.09/0.63    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 2.09/0.63    inference(trivial_inequality_removal,[],[f370])).
% 2.09/0.63  fof(f370,plain,(
% 2.09/0.63    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 2.09/0.63    inference(superposition,[],[f292,f366])).
% 2.09/0.63  fof(f366,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_36),
% 2.09/0.63    inference(avatar_component_clause,[],[f364])).
% 2.09/0.63  fof(f292,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.63    inference(forward_demodulation,[],[f57,f74])).
% 2.09/0.63  fof(f57,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f22])).
% 2.09/0.63  fof(f22,plain,(
% 2.09/0.63    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.63    inference(flattening,[],[f21])).
% 2.09/0.63  fof(f21,plain,(
% 2.09/0.63    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.09/0.63    inference(ennf_transformation,[],[f15])).
% 2.09/0.63  fof(f15,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.09/0.63  fof(f401,plain,(
% 2.09/0.63    spl4_37 | ~spl4_7 | ~spl4_36),
% 2.09/0.63    inference(avatar_split_clause,[],[f400,f364,f120,f376])).
% 2.09/0.63  fof(f400,plain,(
% 2.09/0.63    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_36)),
% 2.09/0.63    inference(subsumption_resolution,[],[f371,f122])).
% 2.09/0.63  fof(f371,plain,(
% 2.09/0.63    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_36),
% 2.09/0.63    inference(superposition,[],[f78,f366])).
% 2.09/0.63  fof(f78,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.63    inference(cnf_transformation,[],[f37])).
% 2.09/0.63  fof(f37,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.63    inference(ennf_transformation,[],[f7])).
% 2.09/0.63  fof(f7,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.09/0.63  fof(f367,plain,(
% 2.09/0.63    spl4_36 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 2.09/0.63    inference(avatar_split_clause,[],[f362,f151,f145,f140,f135,f130,f125,f120,f364])).
% 2.09/0.63  fof(f140,plain,(
% 2.09/0.63    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.09/0.63  fof(f151,plain,(
% 2.09/0.63    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.09/0.63  fof(f362,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f361,f132])).
% 2.09/0.63  fof(f361,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f360,f127])).
% 2.09/0.63  fof(f360,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f359,f122])).
% 2.09/0.63  fof(f359,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f358,f147])).
% 2.09/0.63  fof(f358,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f357,f142])).
% 2.09/0.63  fof(f142,plain,(
% 2.09/0.63    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.09/0.63    inference(avatar_component_clause,[],[f140])).
% 2.09/0.63  fof(f357,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f354,f137])).
% 2.09/0.63  fof(f354,plain,(
% 2.09/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 2.09/0.63    inference(resolution,[],[f353,f153])).
% 2.09/0.63  fof(f153,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.09/0.63    inference(avatar_component_clause,[],[f151])).
% 2.09/0.63  fof(f353,plain,(
% 2.09/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.63    inference(forward_demodulation,[],[f72,f74])).
% 2.09/0.63  fof(f72,plain,(
% 2.09/0.63    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f32])).
% 2.09/0.63  fof(f32,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.63    inference(flattening,[],[f31])).
% 2.09/0.63  fof(f31,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.09/0.63    inference(ennf_transformation,[],[f14])).
% 2.09/0.63  fof(f14,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.09/0.63  fof(f282,plain,(
% 2.09/0.63    spl4_27 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.09/0.63    inference(avatar_split_clause,[],[f277,f151,f145,f135,f130,f120,f279])).
% 2.09/0.63  fof(f277,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f276,f147])).
% 2.09/0.63  fof(f276,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f275,f137])).
% 2.09/0.63  fof(f275,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f274,f132])).
% 2.09/0.63  fof(f274,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.09/0.63    inference(subsumption_resolution,[],[f271,f122])).
% 2.09/0.63  % (23100)Refutation not found, incomplete strategy% (23100)------------------------------
% 2.09/0.63  % (23100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.63  fof(f271,plain,(
% 2.09/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.09/0.63    inference(superposition,[],[f153,f77])).
% 2.09/0.63  % (23100)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.63  
% 2.09/0.63  % (23100)Memory used [KB]: 10746
% 2.09/0.63  % (23100)Time elapsed: 0.207 s
% 2.09/0.63  % (23100)------------------------------
% 2.09/0.63  % (23100)------------------------------
% 2.09/0.63  fof(f266,plain,(
% 2.09/0.63    spl4_26 | ~spl4_10 | ~spl4_22),
% 2.09/0.63    inference(avatar_split_clause,[],[f265,f220,f135,f261])).
% 2.09/0.63  fof(f220,plain,(
% 2.09/0.63    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.09/0.63  fof(f265,plain,(
% 2.09/0.63    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_22)),
% 2.09/0.63    inference(subsumption_resolution,[],[f257,f137])).
% 2.09/0.63  fof(f257,plain,(
% 2.09/0.63    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_22),
% 2.09/0.63    inference(superposition,[],[f81,f222])).
% 2.09/0.63  fof(f222,plain,(
% 2.09/0.63    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_22),
% 2.09/0.63    inference(avatar_component_clause,[],[f220])).
% 2.09/0.63  fof(f81,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.63    inference(cnf_transformation,[],[f39])).
% 2.09/0.63  fof(f39,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.63    inference(ennf_transformation,[],[f6])).
% 2.09/0.63  fof(f6,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.09/0.63  fof(f251,plain,(
% 2.09/0.63    spl4_24 | spl4_25 | ~spl4_9 | ~spl4_14 | ~spl4_23),
% 2.09/0.63    inference(avatar_split_clause,[],[f243,f228,f161,f130,f249,f245])).
% 2.09/0.63  fof(f243,plain,(
% 2.09/0.63    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_9 | ~spl4_14 | ~spl4_23)),
% 2.09/0.63    inference(subsumption_resolution,[],[f242,f163])).
% 2.09/0.64  fof(f242,plain,(
% 2.09/0.64    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) ) | (~spl4_9 | ~spl4_23)),
% 2.09/0.64    inference(subsumption_resolution,[],[f241,f132])).
% 2.09/0.64  fof(f241,plain,(
% 2.09/0.64    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl4_23),
% 2.09/0.64    inference(superposition,[],[f67,f230])).
% 2.09/0.64  fof(f67,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f28])).
% 2.09/0.64  fof(f28,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/0.64    inference(flattening,[],[f27])).
% 2.09/0.64  fof(f27,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f4])).
% 2.09/0.64  fof(f4,axiom,(
% 2.09/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 2.09/0.64  fof(f233,plain,(
% 2.09/0.64    spl4_23 | ~spl4_7 | ~spl4_21),
% 2.09/0.64    inference(avatar_split_clause,[],[f232,f213,f120,f228])).
% 2.09/0.64  fof(f213,plain,(
% 2.09/0.64    spl4_21 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.09/0.64  fof(f232,plain,(
% 2.09/0.64    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_21)),
% 2.09/0.64    inference(subsumption_resolution,[],[f225,f122])).
% 2.09/0.64  fof(f225,plain,(
% 2.09/0.64    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 2.09/0.64    inference(superposition,[],[f81,f215])).
% 2.09/0.64  fof(f215,plain,(
% 2.09/0.64    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_21),
% 2.09/0.64    inference(avatar_component_clause,[],[f213])).
% 2.09/0.64  fof(f223,plain,(
% 2.09/0.64    spl4_22 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.09/0.64    inference(avatar_split_clause,[],[f218,f140,f135,f95,f220])).
% 2.09/0.64  fof(f95,plain,(
% 2.09/0.64    spl4_2 <=> k1_xboole_0 = sK1),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.09/0.64  fof(f218,plain,(
% 2.09/0.64    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.09/0.64    inference(subsumption_resolution,[],[f217,f97])).
% 2.09/0.64  fof(f97,plain,(
% 2.09/0.64    k1_xboole_0 != sK1 | spl4_2),
% 2.09/0.64    inference(avatar_component_clause,[],[f95])).
% 2.09/0.64  fof(f217,plain,(
% 2.09/0.64    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.09/0.64    inference(subsumption_resolution,[],[f208,f142])).
% 2.09/0.64  fof(f208,plain,(
% 2.09/0.64    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.09/0.64    inference(resolution,[],[f60,f137])).
% 2.09/0.64  fof(f60,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.09/0.64    inference(cnf_transformation,[],[f43])).
% 2.09/0.64  fof(f43,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.64    inference(nnf_transformation,[],[f26])).
% 2.09/0.64  fof(f26,plain,(
% 2.09/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.64    inference(flattening,[],[f25])).
% 2.09/0.64  fof(f25,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.64    inference(ennf_transformation,[],[f9])).
% 2.09/0.64  fof(f9,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.09/0.64  fof(f216,plain,(
% 2.09/0.64    spl4_21 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f211,f125,f120,f100,f213])).
% 2.09/0.64  fof(f211,plain,(
% 2.09/0.64    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.09/0.64    inference(subsumption_resolution,[],[f210,f102])).
% 2.09/0.64  fof(f210,plain,(
% 2.09/0.64    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.09/0.64    inference(subsumption_resolution,[],[f207,f127])).
% 2.09/0.64  fof(f207,plain,(
% 2.09/0.64    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.09/0.64    inference(resolution,[],[f60,f122])).
% 2.09/0.64  fof(f193,plain,(
% 2.09/0.64    spl4_18 | ~spl4_6 | ~spl4_10),
% 2.09/0.64    inference(avatar_split_clause,[],[f192,f135,f115,f188])).
% 2.09/0.64  fof(f115,plain,(
% 2.09/0.64    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.09/0.64  fof(f192,plain,(
% 2.09/0.64    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 2.09/0.64    inference(subsumption_resolution,[],[f185,f137])).
% 2.09/0.64  fof(f185,plain,(
% 2.09/0.64    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 2.09/0.64    inference(superposition,[],[f117,f78])).
% 2.09/0.64  fof(f117,plain,(
% 2.09/0.64    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.09/0.64    inference(avatar_component_clause,[],[f115])).
% 2.09/0.64  fof(f170,plain,(
% 2.09/0.64    spl4_15 | ~spl4_10),
% 2.09/0.64    inference(avatar_split_clause,[],[f165,f135,f167])).
% 2.09/0.64  fof(f165,plain,(
% 2.09/0.64    v1_relat_1(sK2) | ~spl4_10),
% 2.09/0.64    inference(subsumption_resolution,[],[f157,f80])).
% 2.09/0.64  fof(f80,plain,(
% 2.09/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f2])).
% 2.09/0.64  fof(f2,axiom,(
% 2.09/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.09/0.64  fof(f157,plain,(
% 2.09/0.64    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.09/0.64    inference(resolution,[],[f79,f137])).
% 2.09/0.64  fof(f79,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f38])).
% 2.09/0.64  fof(f38,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f1])).
% 2.09/0.64  fof(f1,axiom,(
% 2.09/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.09/0.64  fof(f164,plain,(
% 2.09/0.64    spl4_14 | ~spl4_7),
% 2.09/0.64    inference(avatar_split_clause,[],[f159,f120,f161])).
% 2.09/0.64  fof(f159,plain,(
% 2.09/0.64    v1_relat_1(sK3) | ~spl4_7),
% 2.09/0.64    inference(subsumption_resolution,[],[f156,f80])).
% 2.09/0.64  fof(f156,plain,(
% 2.09/0.64    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.09/0.64    inference(resolution,[],[f79,f122])).
% 2.09/0.64  fof(f154,plain,(
% 2.09/0.64    spl4_13 | ~spl4_5),
% 2.09/0.64    inference(avatar_split_clause,[],[f149,f110,f151])).
% 2.09/0.64  fof(f110,plain,(
% 2.09/0.64    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.09/0.64  fof(f149,plain,(
% 2.09/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.09/0.64    inference(backward_demodulation,[],[f112,f74])).
% 2.09/0.64  fof(f112,plain,(
% 2.09/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.09/0.64    inference(avatar_component_clause,[],[f110])).
% 2.09/0.64  fof(f148,plain,(
% 2.09/0.64    spl4_12),
% 2.09/0.64    inference(avatar_split_clause,[],[f45,f145])).
% 2.09/0.64  fof(f45,plain,(
% 2.09/0.64    v1_funct_1(sK2)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f42,plain,(
% 2.09/0.64    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.09/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).
% 2.09/0.64  fof(f40,plain,(
% 2.09/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.09/0.64    introduced(choice_axiom,[])).
% 2.09/0.64  fof(f41,plain,(
% 2.09/0.64    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.09/0.64    introduced(choice_axiom,[])).
% 2.09/0.64  fof(f20,plain,(
% 2.09/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.09/0.64    inference(flattening,[],[f19])).
% 2.09/0.64  fof(f19,plain,(
% 2.09/0.64    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.09/0.64    inference(ennf_transformation,[],[f17])).
% 2.09/0.64  fof(f17,negated_conjecture,(
% 2.09/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.09/0.64    inference(negated_conjecture,[],[f16])).
% 2.09/0.64  fof(f16,conjecture,(
% 2.09/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.09/0.64  fof(f143,plain,(
% 2.09/0.64    spl4_11),
% 2.09/0.64    inference(avatar_split_clause,[],[f46,f140])).
% 2.09/0.64  fof(f46,plain,(
% 2.09/0.64    v1_funct_2(sK2,sK0,sK1)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f138,plain,(
% 2.09/0.64    spl4_10),
% 2.09/0.64    inference(avatar_split_clause,[],[f47,f135])).
% 2.09/0.64  fof(f47,plain,(
% 2.09/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f133,plain,(
% 2.09/0.64    spl4_9),
% 2.09/0.64    inference(avatar_split_clause,[],[f48,f130])).
% 2.09/0.64  fof(f48,plain,(
% 2.09/0.64    v1_funct_1(sK3)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f128,plain,(
% 2.09/0.64    spl4_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f49,f125])).
% 2.09/0.64  fof(f49,plain,(
% 2.09/0.64    v1_funct_2(sK3,sK1,sK0)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f123,plain,(
% 2.09/0.64    spl4_7),
% 2.09/0.64    inference(avatar_split_clause,[],[f50,f120])).
% 2.09/0.64  fof(f50,plain,(
% 2.09/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f118,plain,(
% 2.09/0.64    spl4_6),
% 2.09/0.64    inference(avatar_split_clause,[],[f51,f115])).
% 2.09/0.64  fof(f51,plain,(
% 2.09/0.64    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f113,plain,(
% 2.09/0.64    spl4_5),
% 2.09/0.64    inference(avatar_split_clause,[],[f52,f110])).
% 2.09/0.64  fof(f52,plain,(
% 2.09/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f108,plain,(
% 2.09/0.64    spl4_4),
% 2.09/0.64    inference(avatar_split_clause,[],[f53,f105])).
% 2.09/0.64  fof(f53,plain,(
% 2.09/0.64    v2_funct_1(sK2)),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f103,plain,(
% 2.09/0.64    ~spl4_3),
% 2.09/0.64    inference(avatar_split_clause,[],[f54,f100])).
% 2.09/0.64  fof(f54,plain,(
% 2.09/0.64    k1_xboole_0 != sK0),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f98,plain,(
% 2.09/0.64    ~spl4_2),
% 2.09/0.64    inference(avatar_split_clause,[],[f55,f95])).
% 2.09/0.64  fof(f55,plain,(
% 2.09/0.64    k1_xboole_0 != sK1),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f93,plain,(
% 2.09/0.64    ~spl4_1),
% 2.09/0.64    inference(avatar_split_clause,[],[f56,f90])).
% 2.09/0.64  fof(f56,plain,(
% 2.09/0.64    k2_funct_1(sK2) != sK3),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  % SZS output end Proof for theBenchmark
% 2.09/0.64  % (23105)------------------------------
% 2.09/0.64  % (23105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (23105)Termination reason: Refutation
% 2.09/0.64  
% 2.09/0.64  % (23105)Memory used [KB]: 6652
% 2.09/0.64  % (23105)Time elapsed: 0.196 s
% 2.09/0.64  % (23105)------------------------------
% 2.09/0.64  % (23105)------------------------------
% 2.09/0.64  % (23092)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.09/0.64  % (23094)Refutation not found, incomplete strategy% (23094)------------------------------
% 2.09/0.64  % (23094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (23094)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.64  
% 2.09/0.64  % (23094)Memory used [KB]: 11001
% 2.09/0.64  % (23094)Time elapsed: 0.227 s
% 2.09/0.64  % (23094)------------------------------
% 2.09/0.64  % (23094)------------------------------
% 2.09/0.64  % (23078)Success in time 0.279 s
%------------------------------------------------------------------------------
