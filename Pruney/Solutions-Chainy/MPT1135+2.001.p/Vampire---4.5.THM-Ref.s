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
% DateTime   : Thu Dec  3 13:09:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 396 expanded)
%              Number of leaves         :   45 ( 178 expanded)
%              Depth                    :    8
%              Number of atoms          :  873 (1579 expanded)
%              Number of equality atoms :  164 ( 302 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f56,f60,f64,f68,f72,f76,f80,f84,f88,f92,f99,f107,f111,f117,f130,f136,f140,f147,f151,f156,f169,f173,f180,f187,f196,f245,f260,f270,f281,f320,f349,f393,f465,f501,f521,f535])).

fof(f535,plain,
    ( ~ spl3_4
    | ~ spl3_25
    | ~ spl3_43
    | spl3_50
    | ~ spl3_67 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_25
    | ~ spl3_43
    | spl3_50
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f533,f348])).

fof(f348,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl3_50 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl3_50
  <=> k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f533,plain,
    ( k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_4
    | ~ spl3_25
    | ~ spl3_43
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f532,f280])).

fof(f280,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_43
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f532,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_4
    | ~ spl3_25
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f528,f289])).

fof(f289,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_25
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f528,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_4
    | ~ spl3_67 ),
    inference(resolution,[],[f520,f59])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f520,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) )
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl3_67
  <=> ! [X0] :
        ( k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f521,plain,
    ( spl3_67
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_54
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f510,f499,f391,f105,f54,f46,f519])).

fof(f46,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( spl3_14
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f391,plain,
    ( spl3_54
  <=> k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f499,plain,
    ( spl3_64
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f510,plain,
    ( ! [X0] :
        ( k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_54
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f509,f55])).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f509,plain,
    ( ! [X0] :
        ( k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_54
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f508,f47])).

fof(f47,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f508,plain,
    ( ! [X0] :
        ( k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14
    | ~ spl3_54
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f506,f392])).

fof(f392,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f391])).

fof(f506,plain,
    ( ! [X0] :
        ( k1_pre_topc(sK0,sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14
    | ~ spl3_64 ),
    inference(superposition,[],[f500,f106])).

fof(f106,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f500,plain,
    ( ! [X2,X0,X1] :
        ( k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f499])).

fof(f501,plain,
    ( spl3_64
    | ~ spl3_12
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f492,f463,f90,f499])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

% (5402)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f463,plain,
    ( spl3_62
  <=> ! [X1,X0,X2] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f492,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl3_12
    | ~ spl3_62 ),
    inference(duplicate_literal_removal,[],[f489])).

fof(f489,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_12
    | ~ spl3_62 ),
    inference(resolution,[],[f464,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f464,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f463])).

fof(f465,plain,
    ( spl3_62
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_42
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f356,f318,f268,f119,f105,f54,f46,f463])).

fof(f119,plain,
    ( spl3_17
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f268,plain,
    ( spl3_42
  <=> ! [X3,X5,X2,X4,X6] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(k1_pre_topc(X4,X3))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
        | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f318,plain,
    ( spl3_49
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f356,plain,
    ( ! [X2,X0,X1] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_42
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f355,f326])).

fof(f326,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f325,f106])).

fof(f325,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f321,f47])).

fof(f321,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(resolution,[],[f319,f55])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f318])).

fof(f355,plain,
    ( ! [X2,X0,X1] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f354,f106])).

fof(f354,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f353,f47])).

fof(f353,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f350,f55])).

fof(f350,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_pre_topc(X2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_17
    | ~ spl3_42 ),
    inference(resolution,[],[f344,f269])).

fof(f269,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( ~ l1_pre_topc(k1_pre_topc(X4,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(X2)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
        | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f268])).

fof(f344,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f393,plain,
    ( spl3_54
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f326,f318,f105,f54,f46,f391])).

fof(f349,plain,
    ( ~ spl3_50
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | spl3_15
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f327,f318,f109,f105,f54,f46,f347])).

fof(f109,plain,
    ( spl3_15
  <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f327,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | spl3_15
    | ~ spl3_49 ),
    inference(backward_demodulation,[],[f110,f326])).

fof(f110,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f320,plain,
    ( spl3_49
    | ~ spl3_12
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f264,f258,f90,f318])).

fof(f258,plain,
    ( spl3_41
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_12
    | ~ spl3_41 ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_12
    | ~ spl3_41 ),
    inference(resolution,[],[f259,f91])).

fof(f259,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X2) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f258])).

fof(f281,plain,
    ( spl3_43
    | ~ spl3_1
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f253,f243,f46,f279])).

fof(f243,plain,
    ( spl3_38
  <=> ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f253,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl3_1
    | ~ spl3_38 ),
    inference(resolution,[],[f244,f47])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f243])).

fof(f270,plain,
    ( spl3_42
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f199,f194,f154,f268])).

fof(f154,plain,
    ( spl3_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f194,plain,
    ( spl3_30
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f199,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(k1_pre_topc(X4,X3))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
        | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(k1_pre_topc(X4,X3))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
        | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(resolution,[],[f195,f155])).

fof(f155,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f154])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f194])).

fof(f260,plain,
    ( spl3_41
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f192,f185,f66,f258])).

fof(f66,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f185,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(resolution,[],[f186,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f245,plain,
    ( spl3_38
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f174,f167,f70,f243])).

fof(f70,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f167,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f174,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(resolution,[],[f168,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f167])).

fof(f196,plain,
    ( spl3_30
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f142,f134,f115,f86,f194])).

fof(f86,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f115,plain,
    ( spl3_16
  <=> ! [X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_pre_topc(X0,k2_struct_0(X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f134,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f141,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(superposition,[],[f116,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f116,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_pre_topc(X0,k2_struct_0(X2)) = X2 )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f187,plain,
    ( spl3_28
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f95,f86,f82,f185])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(resolution,[],[f87,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f180,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_27 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | spl3_27 ),
    inference(subsumption_resolution,[],[f177,f47])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_7
    | spl3_27 ),
    inference(resolution,[],[f172,f71])).

fof(f172,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_27
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

% (5411)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f173,plain,
    ( ~ spl3_27
    | ~ spl3_9
    | spl3_25 ),
    inference(avatar_split_clause,[],[f164,f161,f78,f171])).

fof(f78,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f164,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_9
    | spl3_25 ),
    inference(resolution,[],[f162,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f162,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f161])).

fof(f169,plain,
    ( spl3_26
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f94,f82,f78,f74,f167])).

fof(f74,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f93,f79])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
        | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f156,plain,
    ( spl3_23
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f152,f149,f66,f154])).

fof(f149,plain,
    ( spl3_22
  <=> ! [X1,X3,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(X3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f152,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X3,X1) )
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f150,f67])).

fof(f150,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(X3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X3,X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f32,f149])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f147,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f145,f55])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f144,f47])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(resolution,[],[f139,f91])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f140,plain,
    ( spl3_21
    | ~ spl3_6
    | spl3_17 ),
    inference(avatar_split_clause,[],[f126,f119,f66,f138])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6
    | spl3_17 ),
    inference(resolution,[],[f120,f67])).

fof(f120,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f136,plain,
    ( spl3_20
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f132,f128,f90,f86,f134])).

fof(f128,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f131,f91])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f129,f87])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f41,f128])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f117,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) != X1
      | k1_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( ~ spl3_15
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f103,f97,f62,f54,f46,f109])).

fof(f62,plain,
    ( spl3_5
  <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f103,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f63,f102])).

fof(f102,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f98,f55])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f63,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f107,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f102,f97,f54,f46,f105])).

fof(f99,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f88,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f82])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (5408)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f80,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f76,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

% (5411)Refutation not found, incomplete strategy% (5411)------------------------------
% (5411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f66])).

% (5411)Termination reason: Refutation not found, incomplete strategy

% (5411)Memory used [KB]: 10618
% (5411)Time elapsed: 0.094 s
% (5411)------------------------------
% (5411)------------------------------
fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

% (5410)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f64,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f43,f62])).

fof(f43,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(backward_demodulation,[],[f27,f26])).

fof(f26,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
               => ( X1 = X2
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

fof(f27,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f58])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (5401)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (5409)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (5400)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (5393)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (5404)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (5404)Refutation not found, incomplete strategy% (5404)------------------------------
% 0.21/0.49  % (5404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5404)Memory used [KB]: 1663
% 0.21/0.49  % (5404)Time elapsed: 0.040 s
% 0.21/0.49  % (5404)------------------------------
% 0.21/0.49  % (5404)------------------------------
% 0.21/0.49  % (5391)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (5399)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (5398)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (5405)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5394)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5397)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (5407)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (5392)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (5400)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5396)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5392)Refutation not found, incomplete strategy% (5392)------------------------------
% 0.21/0.50  % (5392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5392)Memory used [KB]: 10618
% 0.21/0.50  % (5395)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (5392)Time elapsed: 0.075 s
% 0.21/0.50  % (5392)------------------------------
% 0.21/0.50  % (5392)------------------------------
% 0.21/0.51  % (5391)Refutation not found, incomplete strategy% (5391)------------------------------
% 0.21/0.51  % (5391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5391)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5391)Memory used [KB]: 6396
% 0.21/0.51  % (5391)Time elapsed: 0.062 s
% 0.21/0.51  % (5391)------------------------------
% 0.21/0.51  % (5391)------------------------------
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f542,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f48,f56,f60,f64,f68,f72,f76,f80,f84,f88,f92,f99,f107,f111,f117,f130,f136,f140,f147,f151,f156,f169,f173,f180,f187,f196,f245,f260,f270,f281,f320,f349,f393,f465,f501,f521,f535])).
% 0.21/0.51  fof(f535,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_25 | ~spl3_43 | spl3_50 | ~spl3_67),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f534])).
% 0.21/0.51  fof(f534,plain,(
% 0.21/0.51    $false | (~spl3_4 | ~spl3_25 | ~spl3_43 | spl3_50 | ~spl3_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f533,f348])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl3_50),
% 0.21/0.51    inference(avatar_component_clause,[],[f347])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    spl3_50 <=> k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.51  fof(f533,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_4 | ~spl3_25 | ~spl3_43 | ~spl3_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f532,f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f279])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    spl3_43 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f532,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_4 | ~spl3_25 | ~spl3_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f528,f289])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl3_25 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f528,plain,(
% 0.21/0.51    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_4 | ~spl3_67)),
% 0.21/0.51    inference(resolution,[],[f520,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f520,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)) ) | ~spl3_67),
% 0.21/0.51    inference(avatar_component_clause,[],[f519])).
% 0.21/0.51  fof(f519,plain,(
% 0.21/0.51    spl3_67 <=> ! [X0] : (k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.21/0.51  fof(f521,plain,(
% 0.21/0.51    spl3_67 | ~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_54 | ~spl3_64),
% 0.21/0.51    inference(avatar_split_clause,[],[f510,f499,f391,f105,f54,f46,f519])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl3_14 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    spl3_54 <=> k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.51  fof(f499,plain,(
% 0.21/0.51    spl3_64 <=> ! [X1,X0,X2] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.51  fof(f510,plain,(
% 0.21/0.51    ( ! [X0] : (k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_54 | ~spl3_64)),
% 0.21/0.51    inference(subsumption_resolution,[],[f509,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f509,plain,(
% 0.21/0.51    ( ! [X0] : (k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_14 | ~spl3_54 | ~spl3_64)),
% 0.21/0.51    inference(subsumption_resolution,[],[f508,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f508,plain,(
% 0.21/0.51    ( ! [X0] : (k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_14 | ~spl3_54 | ~spl3_64)),
% 0.21/0.51    inference(subsumption_resolution,[],[f506,f392])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~spl3_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f391])).
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    ( ! [X0] : (k1_pre_topc(sK0,sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_14 | ~spl3_64)),
% 0.21/0.51    inference(superposition,[],[f500,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f500,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl3_64),
% 0.21/0.51    inference(avatar_component_clause,[],[f499])).
% 0.21/0.51  fof(f501,plain,(
% 0.21/0.51    spl3_64 | ~spl3_12 | ~spl3_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f492,f463,f90,f499])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_12 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  % (5402)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    spl3_62 <=> ! [X1,X0,X2] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) ) | (~spl3_12 | ~spl3_62)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f489])).
% 0.21/0.51  fof(f489,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | k1_pre_topc(sK0,sK1) != g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | (~spl3_12 | ~spl3_62)),
% 0.21/0.51    inference(resolution,[],[f464,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1) | ~l1_pre_topc(X1)) ) | ~spl3_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f463])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    spl3_62 | ~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_17 | ~spl3_42 | ~spl3_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f356,f318,f268,f119,f105,f54,f46,f463])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl3_17 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    spl3_42 <=> ! [X3,X5,X2,X4,X6] : (~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~l1_pre_topc(k1_pre_topc(X4,X3)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3))) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    spl3_49 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) | ~l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_17 | ~spl3_42 | ~spl3_49)),
% 0.21/0.51    inference(forward_demodulation,[],[f355,f326])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | (~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_49)),
% 0.21/0.51    inference(forward_demodulation,[],[f325,f106])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | (~spl3_1 | ~spl3_3 | ~spl3_49)),
% 0.21/0.51    inference(subsumption_resolution,[],[f321,f47])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_49)),
% 0.21/0.51    inference(resolution,[],[f319,f55])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) ) | ~spl3_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f318])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_17 | ~spl3_42)),
% 0.21/0.51    inference(forward_demodulation,[],[f354,f106])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_17 | ~spl3_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f353,f47])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) ) | (~spl3_3 | ~spl3_17 | ~spl3_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f350,f55])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) ) | (~spl3_17 | ~spl3_42)),
% 0.21/0.51    inference(resolution,[],[f344,f269])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X5,X3] : (~l1_pre_topc(k1_pre_topc(X4,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3))) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5)) ) | ~spl3_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f268])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    spl3_54 | ~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f326,f318,f105,f54,f46,f391])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    ~spl3_50 | ~spl3_1 | ~spl3_3 | ~spl3_14 | spl3_15 | ~spl3_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f327,f318,f109,f105,f54,f46,f347])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl3_15 <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_1 | ~spl3_3 | ~spl3_14 | spl3_15 | ~spl3_49)),
% 0.21/0.51    inference(backward_demodulation,[],[f110,f326])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    spl3_49 | ~spl3_12 | ~spl3_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f264,f258,f90,f318])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl3_41 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) ) | (~spl3_12 | ~spl3_41)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | (~spl3_12 | ~spl3_41)),
% 0.21/0.51    inference(resolution,[],[f259,f91])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2)) ) | ~spl3_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    spl3_43 | ~spl3_1 | ~spl3_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f253,f243,f46,f279])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    spl3_38 <=> ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl3_1 | ~spl3_38)),
% 0.21/0.51    inference(resolution,[],[f244,f47])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) | ~spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f243])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl3_42 | ~spl3_23 | ~spl3_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f199,f194,f154,f268])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl3_23 <=> ! [X1,X3,X0,X2] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    spl3_30 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X5,X3] : (~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~l1_pre_topc(k1_pre_topc(X4,X3)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3))) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5)) ) | (~spl3_23 | ~spl3_30)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X5,X3] : (~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_pre_topc(X4,X3) = k1_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~l1_pre_topc(X2) | ~l1_pre_topc(k1_pre_topc(X4,X3)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) | g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) != g1_pre_topc(u1_struct_0(k1_pre_topc(X4,X3)),u1_pre_topc(k1_pre_topc(X4,X3))) | ~m1_pre_topc(X6,X5) | ~l1_pre_topc(X5)) ) | (~spl3_23 | ~spl3_30)),
% 0.21/0.51    inference(resolution,[],[f195,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) ) | ~spl3_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f194])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    spl3_41 | ~spl3_6 | ~spl3_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f192,f185,f66,f258])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl3_6 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl3_28 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(k1_pre_topc(X1,X0)) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2)) ) | (~spl3_6 | ~spl3_28)),
% 0.21/0.51    inference(resolution,[],[f186,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(k1_pre_topc(X1,X0)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))) ) | ~spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl3_38 | ~spl3_7 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f167,f70,f243])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl3_7 <=> ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl3_26 <=> ! [X1,X0] : (g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0)) ) | (~spl3_7 | ~spl3_26)),
% 0.21/0.51    inference(resolution,[],[f168,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))) ) | ~spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f167])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    spl3_30 | ~spl3_11 | ~spl3_16 | ~spl3_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f142,f134,f115,f86,f194])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl3_11 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl3_16 <=> ! [X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl3_20 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl3_11 | ~spl3_16 | ~spl3_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl3_16 | ~spl3_20)),
% 0.21/0.51    inference(superposition,[],[f116,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2) ) | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl3_28 | ~spl3_10 | ~spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f95,f86,f82,f185])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl3_10 <=> ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(k1_pre_topc(X1,X0)) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.51    inference(resolution,[],[f87,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) ) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_7 | spl3_27),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    $false | (~spl3_1 | ~spl3_7 | spl3_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f47])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | (~spl3_7 | spl3_27)),
% 0.21/0.51    inference(resolution,[],[f172,f71])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl3_27 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  % (5411)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~spl3_27 | ~spl3_9 | spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f164,f161,f78,f171])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl3_9 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_9 | spl3_25)),
% 0.21/0.51    inference(resolution,[],[f162,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl3_26 | ~spl3_8 | ~spl3_9 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f82,f78,f74,f167])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl3_8 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_8 | ~spl3_9 | ~spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f79])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(g1_pre_topc(X0,X1)) | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.51    inference(resolution,[],[f83,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl3_23 | ~spl3_6 | ~spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f149,f66,f154])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl3_22 <=> ! [X1,X3,X0,X2] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) ) | (~spl3_6 | ~spl3_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f67])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) ) | ~spl3_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f149])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_3 | ~spl3_12 | ~spl3_21),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    $false | (~spl3_1 | ~spl3_3 | ~spl3_12 | ~spl3_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f55])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_12 | ~spl3_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f47])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_12 | ~spl3_21)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_12 | ~spl3_21)),
% 0.21/0.51    inference(resolution,[],[f139,f91])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl3_21 <=> ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl3_21 | ~spl3_6 | spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f126,f119,f66,f138])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_6 | spl3_17)),
% 0.21/0.51    inference(resolution,[],[f120,f67])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl3_20 | ~spl3_11 | ~spl3_12 | ~spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f132,f128,f90,f86,f134])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl3_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_11 | ~spl3_12 | ~spl3_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f91])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_11 | ~spl3_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f87])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f128])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f128])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f115])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) != X1 | k1_pre_topc(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~spl3_15 | ~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f97,f62,f54,f46,f109])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl3_5 <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl3_13 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) | (~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_13)),
% 0.21/0.51    inference(backward_demodulation,[],[f63,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f47])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_13)),
% 0.21/0.51    inference(resolution,[],[f98,f55])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl3_14 | ~spl3_1 | ~spl3_3 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f97,f54,f46,f105])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f97])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f90])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f86])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f82])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  % (5408)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f78])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f74])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  % (5411)Refutation not found, incomplete strategy% (5411)------------------------------
% 0.21/0.51  % (5411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.51  % (5411)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5411)Memory used [KB]: 10618
% 0.21/0.51  % (5411)Time elapsed: 0.094 s
% 0.21/0.51  % (5411)------------------------------
% 0.21/0.51  % (5411)------------------------------
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  % (5410)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f62])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f27,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    sK1 = sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) & X1 = X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f58])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.51    inference(forward_demodulation,[],[f25,f26])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f46])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5400)------------------------------
% 0.21/0.51  % (5400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5400)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5400)Memory used [KB]: 11001
% 0.21/0.51  % (5400)Time elapsed: 0.073 s
% 0.21/0.51  % (5400)------------------------------
% 0.21/0.51  % (5400)------------------------------
% 0.21/0.51  % (5390)Success in time 0.15 s
%------------------------------------------------------------------------------
