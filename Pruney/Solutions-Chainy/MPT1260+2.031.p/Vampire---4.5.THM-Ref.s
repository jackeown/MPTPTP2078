%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:37 EST 2020

% Result     : Theorem 31.56s
% Output     : Refutation 31.56s
% Verified   : 
% Statistics : Number of formulae       :  653 (3891 expanded)
%              Number of leaves         :  159 (1419 expanded)
%              Depth                    :   23
%              Number of atoms          : 1973 (10951 expanded)
%              Number of equality atoms :  452 (3239 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46931,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f147,f152,f157,f162,f558,f593,f603,f661,f806,f821,f827,f1582,f1613,f1646,f1653,f1668,f1734,f1821,f1852,f1864,f1887,f1924,f1946,f2710,f3652,f3714,f4438,f5657,f5661,f5662,f5668,f5670,f5672,f5680,f5682,f5694,f5700,f5782,f5785,f5786,f5792,f5796,f5800,f5804,f5805,f5933,f5936,f5944,f5958,f5968,f6036,f6068,f6070,f6136,f6138,f6142,f6144,f6255,f6437,f6587,f6663,f6749,f7116,f7830,f8224,f8267,f9254,f9276,f9277,f9294,f9410,f10672,f10731,f10733,f10761,f10845,f11062,f11197,f11283,f11499,f11830,f12577,f19493,f23101,f23184,f23186,f23201,f23374,f23414,f23419,f23490,f23598,f24902,f24907,f25519,f25896,f25997,f26109,f26192,f26349,f26528,f26685,f26834,f26860,f26980,f27622,f29129,f30537,f30544,f30551,f40724,f41833,f41838,f41843,f46873,f46892,f46895,f46899,f46906,f46918,f46919,f46920,f46922,f46927])).

fof(f46927,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))
    | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) != k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46922,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1)
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46920,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))))
    | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46919,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))))
    | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46918,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0)
    | ~ v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46906,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))))
    | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | sK1 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46899,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) != k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46895,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46892,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))
    | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1))))
    | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) != k3_subset_1(sK1,k5_xboole_0(sK1,sK1))
    | k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))))
    | k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f46873,plain,
    ( ~ spl4_1892
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_1893 ),
    inference(avatar_split_clause,[],[f46801,f41840,f216,f143,f41835])).

fof(f41835,plain,
    ( spl4_1892
  <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1892])])).

fof(f143,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f216,plain,
    ( spl4_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f41840,plain,
    ( spl4_1893
  <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1893])])).

fof(f46801,plain,
    ( ~ r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_1893 ),
    inference(unit_resulting_resolution,[],[f41842,f3457])).

fof(f3457,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f1783,f144])).

fof(f144,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1783,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X13))
        | ~ r2_hidden(X14,X13) )
    | ~ spl4_9 ),
    inference(superposition,[],[f133,f298])).

fof(f298,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0)))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f218,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f95,f108])).

fof(f108,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f218,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f216])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f97,f108])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f41842,plain,
    ( r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_1893 ),
    inference(avatar_component_clause,[],[f41840])).

fof(f41843,plain,
    ( spl4_1893
    | spl4_566
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_358
    | ~ spl4_989 ),
    inference(avatar_split_clause,[],[f41699,f19490,f4309,f845,f149,f11054,f41840])).

fof(f11054,plain,
    ( spl4_566
  <=> k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_566])])).

fof(f149,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f845,plain,
    ( spl4_76
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f4309,plain,
    ( spl4_358
  <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_358])])).

fof(f19490,plain,
    ( spl4_989
  <=> k1_xboole_0 = k7_subset_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_989])])).

fof(f41699,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_358
    | ~ spl4_989 ),
    inference(resolution,[],[f41634,f4362])).

fof(f4362,plain,
    ( ! [X16] :
        ( ~ r2_hidden(X16,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
        | r2_hidden(X16,sK1) )
    | ~ spl4_358 ),
    inference(superposition,[],[f137,f4311])).

fof(f4311,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_358 ),
    inference(avatar_component_clause,[],[f4309])).

fof(f137,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f102,f82])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f41634,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK1,sK1,X3),X3)
        | k1_xboole_0 = X3 )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_989 ),
    inference(duplicate_literal_removal,[],[f41633])).

fof(f41633,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 = X3
        | r2_hidden(sK2(sK1,sK1,X3),X3) )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_989 ),
    inference(forward_demodulation,[],[f41632,f19492])).

fof(f19492,plain,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,sK1)
    | ~ spl4_989 ),
    inference(avatar_component_clause,[],[f19490])).

fof(f41632,plain,
    ( ! [X3] :
        ( k7_subset_1(sK1,sK1,sK1) = X3
        | k1_xboole_0 = X3
        | r2_hidden(sK2(sK1,sK1,X3),X3) )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_989 ),
    inference(forward_demodulation,[],[f41631,f19510])).

fof(f19510,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(sK1,sK1,X0)
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(backward_demodulation,[],[f491,f19406])).

fof(f19406,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(backward_demodulation,[],[f181,f941])).

fof(f941,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0)
    | ~ spl4_76 ),
    inference(unit_resulting_resolution,[],[f847,f119])).

fof(f847,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f845])).

fof(f181,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f151,f119])).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f491,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1)))
    | ~ spl4_3 ),
    inference(superposition,[],[f181,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41631,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | r2_hidden(sK2(sK1,sK1,X3),X3)
        | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3 )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_989 ),
    inference(forward_demodulation,[],[f41607,f19492])).

fof(f41607,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK1,sK1,X3),X3)
        | k7_subset_1(sK1,sK1,sK1) = X3
        | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3 )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(duplicate_literal_removal,[],[f41587])).

fof(f41587,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK1,sK1,X3),X3)
        | k7_subset_1(sK1,sK1,sK1) = X3
        | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3
        | r2_hidden(sK2(sK1,sK1,X3),X3) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(resolution,[],[f21048,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f100,f108])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f21048,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK1,X0,X1),X1)
        | r2_hidden(sK2(sK1,X0,X1),sK1)
        | k7_subset_1(sK1,sK1,X0) = X1 )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(condensation,[],[f20993])).

fof(f20993,plain,
    ( ! [X8,X7,X9] :
        ( r2_hidden(sK2(sK1,X7,X8),X8)
        | k7_subset_1(sK1,sK1,X7) = X8
        | r2_hidden(sK2(sK1,X7,X8),X9)
        | r2_hidden(sK2(sK1,X7,X8),sK1) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(resolution,[],[f19599,f19514])).

fof(f19514,plain,
    ( ! [X15,X16] :
        ( ~ r2_hidden(X16,k7_subset_1(sK1,sK1,X15))
        | r2_hidden(X16,sK1) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(backward_demodulation,[],[f516,f19406])).

fof(f516,plain,
    ( ! [X15,X16] :
        ( ~ r2_hidden(X16,k7_subset_1(u1_struct_0(sK0),sK1,X15))
        | r2_hidden(X16,sK1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f134,f181])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f96,f108])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f19599,plain,
    ( ! [X10,X11,X9] :
        ( r2_hidden(sK2(sK1,X9,X10),k7_subset_1(sK1,sK1,X11))
        | r2_hidden(sK2(sK1,X9,X10),X10)
        | k7_subset_1(sK1,sK1,X9) = X10
        | r2_hidden(sK2(sK1,X9,X10),X11) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f19542,f19406])).

fof(f19542,plain,
    ( ! [X10,X11,X9] :
        ( k7_subset_1(sK1,sK1,X9) = X10
        | r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11))
        | r2_hidden(sK2(sK1,X9,X10),X10)
        | r2_hidden(sK2(sK1,X9,X10),X11) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(backward_demodulation,[],[f1563,f19406])).

fof(f1563,plain,
    ( ! [X10,X11,X9] :
        ( r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11))
        | r2_hidden(sK2(sK1,X9,X10),X10)
        | k7_subset_1(u1_struct_0(sK0),sK1,X9) = X10
        | r2_hidden(sK2(sK1,X9,X10),X11) )
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1554,f181])).

fof(f1554,plain,
    ( ! [X10,X11,X9] :
        ( r2_hidden(sK2(sK1,X9,X10),X11)
        | r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11))
        | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X9))) = X10
        | r2_hidden(sK2(sK1,X9,X10),X10) )
    | ~ spl4_3 ),
    inference(resolution,[],[f514,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f99,f108])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f514,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(X12,sK1)
        | r2_hidden(X12,X11)
        | r2_hidden(X12,k7_subset_1(u1_struct_0(sK0),sK1,X11)) )
    | ~ spl4_3 ),
    inference(superposition,[],[f132,f181])).

fof(f132,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f98,f108])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f41838,plain,
    ( spl4_1892
    | spl4_566
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_358
    | ~ spl4_989 ),
    inference(avatar_split_clause,[],[f41698,f19490,f4309,f845,f149,f11054,f41835])).

fof(f41698,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_358
    | ~ spl4_989 ),
    inference(resolution,[],[f41634,f4361])).

fof(f4361,plain,
    ( ! [X15] :
        ( ~ r2_hidden(X15,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
        | r2_hidden(X15,k2_tops_1(sK0,sK1)) )
    | ~ spl4_358 ),
    inference(superposition,[],[f136,f4311])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f103,f82])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f41833,plain,
    ( ~ spl4_1891
    | spl4_566
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_368
    | ~ spl4_989 ),
    inference(avatar_split_clause,[],[f41697,f19490,f4435,f845,f149,f11054,f41830])).

fof(f41830,plain,
    ( spl4_1891
  <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1891])])).

fof(f4435,plain,
    ( spl4_368
  <=> k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_368])])).

fof(f41697,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_368
    | ~ spl4_989 ),
    inference(resolution,[],[f41634,f4441])).

fof(f4441,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl4_3
    | ~ spl4_368 ),
    inference(superposition,[],[f515,f4437])).

fof(f4437,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_368 ),
    inference(avatar_component_clause,[],[f4435])).

fof(f515,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),sK1,X13))
        | ~ r2_hidden(X14,X13) )
    | ~ spl4_3 ),
    inference(superposition,[],[f133,f181])).

fof(f40724,plain,
    ( sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | k2_pre_topc(sK0,sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) != k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f30551,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f30544,plain,
    ( spl4_1422
    | ~ spl4_18
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(avatar_split_clause,[],[f30539,f29126,f23150,f5203,f285,f30541])).

fof(f30541,plain,
    ( spl4_1422
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1422])])).

fof(f285,plain,
    ( spl4_18
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f5203,plain,
    ( spl4_428
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_428])])).

fof(f23150,plain,
    ( spl4_1089
  <=> u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1089])])).

fof(f29126,plain,
    ( spl4_1377
  <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1377])])).

fof(f30539,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_18
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(forward_demodulation,[],[f30538,f287])).

fof(f287,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f285])).

fof(f30538,plain,
    ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(forward_demodulation,[],[f30526,f81])).

fof(f30526,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(superposition,[],[f27039,f29128])).

fof(f29128,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | ~ spl4_1377 ),
    inference(avatar_component_clause,[],[f29126])).

fof(f27039,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(u1_struct_0(sK0),X1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1))
    | ~ spl4_428
    | ~ spl4_1089 ),
    inference(backward_demodulation,[],[f23456,f23151])).

fof(f23151,plain,
    ( u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_1089 ),
    inference(avatar_component_clause,[],[f23150])).

fof(f23456,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))
    | ~ spl4_428 ),
    inference(forward_demodulation,[],[f23430,f11996])).

fof(f11996,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0)))
    | ~ spl4_428 ),
    inference(unit_resulting_resolution,[],[f5205,f119])).

fof(f5205,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_428 ),
    inference(avatar_component_clause,[],[f5203])).

fof(f23430,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))))
    | ~ spl4_428 ),
    inference(superposition,[],[f11996,f113])).

fof(f113,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f84,f82,f108,f108])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30537,plain,
    ( spl4_1421
    | ~ spl4_18
    | ~ spl4_75
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(avatar_split_clause,[],[f30532,f29126,f23150,f5203,f834,f285,f30534])).

fof(f30534,plain,
    ( spl4_1421
  <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1421])])).

fof(f834,plain,
    ( spl4_75
  <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f30532,plain,
    ( sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_18
    | ~ spl4_75
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(forward_demodulation,[],[f30531,f287])).

fof(f30531,plain,
    ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_75
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(forward_demodulation,[],[f30530,f81])).

fof(f30530,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_75
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(forward_demodulation,[],[f30524,f836])).

fof(f836,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f834])).

fof(f30524,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_428
    | ~ spl4_1089
    | ~ spl4_1377 ),
    inference(superposition,[],[f27035,f29128])).

fof(f27035,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(u1_struct_0(sK0),X1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1))))
    | ~ spl4_428
    | ~ spl4_1089 ),
    inference(backward_demodulation,[],[f23438,f23151])).

fof(f23438,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))))
    | ~ spl4_428 ),
    inference(superposition,[],[f113,f11996])).

fof(f29129,plain,
    ( spl4_1377
    | ~ spl4_18
    | ~ spl4_428
    | ~ spl4_1089 ),
    inference(avatar_split_clause,[],[f29106,f23150,f5203,f285,f29126])).

fof(f29106,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | ~ spl4_18
    | ~ spl4_428
    | ~ spl4_1089 ),
    inference(superposition,[],[f27033,f287])).

fof(f27033,plain,
    ( ! [X0] : k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0)))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)
    | ~ spl4_428
    | ~ spl4_1089 ),
    inference(backward_demodulation,[],[f23420,f23151])).

fof(f23420,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(X0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl4_428 ),
    inference(superposition,[],[f11996,f81])).

fof(f27622,plain,
    ( spl4_1334
    | ~ spl4_123
    | ~ spl4_601 ),
    inference(avatar_split_clause,[],[f27558,f12069,f1323,f27608])).

fof(f27608,plain,
    ( spl4_1334
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1334])])).

fof(f1323,plain,
    ( spl4_123
  <=> k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f12069,plain,
    ( spl4_601
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_601])])).

fof(f27558,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_123
    | ~ spl4_601 ),
    inference(superposition,[],[f1325,f12079])).

fof(f12079,plain,
    ( ! [X0] : k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)
    | ~ spl4_601 ),
    inference(unit_resulting_resolution,[],[f12071,f119])).

fof(f12071,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_601 ),
    inference(avatar_component_clause,[],[f12069])).

fof(f1325,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))))
    | ~ spl4_123 ),
    inference(avatar_component_clause,[],[f1323])).

fof(f26980,plain,
    ( spl4_432
    | ~ spl4_4
    | ~ spl4_425
    | ~ spl4_428 ),
    inference(avatar_split_clause,[],[f26977,f5203,f5188,f154,f5223])).

fof(f5223,plain,
    ( spl4_432
  <=> k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_432])])).

fof(f154,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f5188,plain,
    ( spl4_425
  <=> v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_425])])).

fof(f26977,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_425
    | ~ spl4_428 ),
    inference(unit_resulting_resolution,[],[f156,f5205,f5189,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f5189,plain,
    ( v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl4_425 ),
    inference(avatar_component_clause,[],[f5188])).

fof(f156,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f26860,plain,
    ( spl4_595
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150
    | ~ spl4_167
    | ~ spl4_407
    | ~ spl4_412 ),
    inference(avatar_split_clause,[],[f26859,f5116,f5089,f1936,f1659,f529,f149,f11961])).

fof(f11961,plain,
    ( spl4_595
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_595])])).

fof(f529,plain,
    ( spl4_44
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1659,plain,
    ( spl4_150
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f1936,plain,
    ( spl4_167
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).

fof(f5089,plain,
    ( spl4_407
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_407])])).

fof(f5116,plain,
    ( spl4_412
  <=> k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_412])])).

fof(f26859,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150
    | ~ spl4_167
    | ~ spl4_407
    | ~ spl4_412 ),
    inference(forward_demodulation,[],[f5118,f11828])).

fof(f11828,plain,
    ( ! [X0] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150
    | ~ spl4_167
    | ~ spl4_407 ),
    inference(forward_demodulation,[],[f11827,f1938])).

fof(f1938,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_167 ),
    inference(avatar_component_clause,[],[f1936])).

fof(f11827,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150
    | ~ spl4_407 ),
    inference(forward_demodulation,[],[f11797,f1894])).

fof(f1894,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150 ),
    inference(unit_resulting_resolution,[],[f1862,f1862,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f105,f82])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1862,plain,
    ( ! [X15] : ~ r2_hidden(X15,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f1845,f1262])).

fof(f1262,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(superposition,[],[f515,f531])).

fof(f531,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f529])).

fof(f1845,plain,
    ( ! [X15] :
        ( ~ r2_hidden(X15,k1_xboole_0)
        | r2_hidden(X15,sK1) )
    | ~ spl4_150 ),
    inference(superposition,[],[f136,f1661])).

fof(f1661,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f1659])).

fof(f11797,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)
    | ~ spl4_407 ),
    inference(unit_resulting_resolution,[],[f5091,f119])).

fof(f5091,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_407 ),
    inference(avatar_component_clause,[],[f5089])).

fof(f5118,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))
    | ~ spl4_412 ),
    inference(avatar_component_clause,[],[f5116])).

fof(f26834,plain,
    ( spl4_405
    | ~ spl4_410
    | ~ spl4_595 ),
    inference(avatar_split_clause,[],[f12172,f11961,f5106,f5079])).

fof(f5079,plain,
    ( spl4_405
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_405])])).

fof(f5106,plain,
    ( spl4_410
  <=> v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_410])])).

fof(f12172,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_410
    | ~ spl4_595 ),
    inference(backward_demodulation,[],[f5108,f11963])).

fof(f11963,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl4_595 ),
    inference(avatar_component_clause,[],[f11961])).

fof(f5108,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0)
    | ~ spl4_410 ),
    inference(avatar_component_clause,[],[f5106])).

fof(f26685,plain,
    ( spl4_412
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f26648,f1659,f1579,f845,f529,f154,f149,f5116])).

fof(f1579,plain,
    ( spl4_144
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f26648,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(unit_resulting_resolution,[],[f156,f26529,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f26529,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(unit_resulting_resolution,[],[f25874,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f25874,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(superposition,[],[f112,f22985])).

fof(f22985,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X3,k1_xboole_0))))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(superposition,[],[f113,f22914])).

fof(f22914,plain,
    ( ! [X4] : k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4)))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f22910,f1862])).

fof(f22910,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4)))
        | r2_hidden(sK3(X4,k7_subset_1(sK1,sK1,X4),k1_xboole_0),k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_144 ),
    inference(duplicate_literal_removal,[],[f22868])).

fof(f22868,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4)))
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4)))
        | r2_hidden(sK3(X4,k7_subset_1(sK1,sK1,X4),k1_xboole_0),k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_76
    | ~ spl4_144 ),
    inference(resolution,[],[f16499,f19575])).

fof(f19575,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25)
        | k1_setfam_1(k2_tarski(X24,k7_subset_1(sK1,sK1,X25))) = X26
        | r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X26) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f19574,f19406])).

fof(f19574,plain,
    ( ! [X26,X24,X25] :
        ( k1_setfam_1(k2_tarski(X24,k7_subset_1(sK1,sK1,X25))) = X26
        | ~ r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25)
        | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f19523,f19406])).

fof(f19523,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25)
        | k1_setfam_1(k2_tarski(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25))) = X26
        | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26) )
    | ~ spl4_3
    | ~ spl4_76 ),
    inference(backward_demodulation,[],[f1257,f19406])).

fof(f1257,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X25)
        | k1_setfam_1(k2_tarski(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25))) = X26
        | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26) )
    | ~ spl4_3 ),
    inference(resolution,[],[f515,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f106,f82])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f16499,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3)) )
    | ~ spl4_3
    | ~ spl4_144 ),
    inference(forward_demodulation,[],[f16498,f1581])).

fof(f1581,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl4_144 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f16498,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k1_xboole_0),X2)
        | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3)) )
    | ~ spl4_3
    | ~ spl4_144 ),
    inference(forward_demodulation,[],[f16493,f1581])).

fof(f16493,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2)
        | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3)) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f16409])).

fof(f16409,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2)
        | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3))
        | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3))
        | r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f1274,f1258])).

fof(f1258,plain,
    ( ! [X28,X29,X27] :
        ( ~ r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X29)
        | k7_subset_1(u1_struct_0(sK0),sK1,X29) = k1_setfam_1(k2_tarski(X27,X28))
        | r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X27) )
    | ~ spl4_3 ),
    inference(resolution,[],[f515,f128])).

fof(f1274,plain,
    ( ! [X28,X29,X27] :
        ( r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),sK1)
        | r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X27)
        | k7_subset_1(u1_struct_0(sK0),sK1,X29) = k1_setfam_1(k2_tarski(X27,X28)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f516,f128])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f80,f108])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26528,plain,
    ( spl4_588
    | ~ spl4_407 ),
    inference(avatar_split_clause,[],[f26527,f5089,f11822])).

fof(f11822,plain,
    ( spl4_588
  <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_588])])).

fof(f26527,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_407 ),
    inference(forward_demodulation,[],[f26500,f110])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f70,f108])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f26500,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_407 ),
    inference(resolution,[],[f5091,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f87,f108])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f26349,plain,
    ( spl4_407
    | ~ spl4_408 ),
    inference(avatar_split_clause,[],[f11866,f5096,f5089])).

fof(f5096,plain,
    ( spl4_408
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_408])])).

fof(f11866,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_408 ),
    inference(unit_resulting_resolution,[],[f5098,f91])).

fof(f5098,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_408 ),
    inference(avatar_component_clause,[],[f5096])).

fof(f26192,plain,
    ( spl4_630
    | ~ spl4_491 ),
    inference(avatar_split_clause,[],[f12509,f5536,f12527])).

fof(f12527,plain,
    ( spl4_630
  <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_630])])).

fof(f5536,plain,
    ( spl4_491
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_491])])).

fof(f12509,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | ~ spl4_491 ),
    inference(unit_resulting_resolution,[],[f5538,f115])).

fof(f5538,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_491 ),
    inference(avatar_component_clause,[],[f5536])).

fof(f26109,plain,
    ( ~ spl4_407
    | spl4_601
    | ~ spl4_588 ),
    inference(avatar_split_clause,[],[f11981,f11822,f12069,f5089])).

fof(f11981,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_588 ),
    inference(superposition,[],[f86,f11824])).

fof(f11824,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_588 ),
    inference(avatar_component_clause,[],[f11822])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f25997,plain,
    ( spl4_643
    | ~ spl4_641 ),
    inference(avatar_split_clause,[],[f12710,f12692,f12727])).

fof(f12727,plain,
    ( spl4_643
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_643])])).

fof(f12692,plain,
    ( spl4_641
  <=> k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_641])])).

fof(f12710,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | ~ spl4_641 ),
    inference(superposition,[],[f113,f12694])).

fof(f12694,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl4_641 ),
    inference(avatar_component_clause,[],[f12692])).

fof(f25896,plain,
    ( spl4_1144
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | ~ spl4_596 ),
    inference(avatar_split_clause,[],[f25845,f12016,f1659,f1579,f845,f529,f149,f23951])).

fof(f23951,plain,
    ( spl4_1144
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1144])])).

fof(f12016,plain,
    ( spl4_596
  <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_596])])).

fof(f25845,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | ~ spl4_596 ),
    inference(backward_demodulation,[],[f12018,f22985])).

fof(f12018,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl4_596 ),
    inference(avatar_component_clause,[],[f12016])).

fof(f25519,plain,
    ( spl4_1235
    | ~ spl4_1188 ),
    inference(avatar_split_clause,[],[f25518,f24899,f25509])).

fof(f25509,plain,
    ( spl4_1235
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1235])])).

fof(f24899,plain,
    ( spl4_1188
  <=> r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1188])])).

fof(f25518,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | ~ spl4_1188 ),
    inference(forward_demodulation,[],[f25502,f81])).

fof(f25502,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0)))
    | ~ spl4_1188 ),
    inference(resolution,[],[f24901,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f82])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f24901,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0))
    | ~ spl4_1188 ),
    inference(avatar_component_clause,[],[f24899])).

fof(f24907,plain,
    ( spl4_1189
    | ~ spl4_1103 ),
    inference(avatar_split_clause,[],[f24882,f23416,f24904])).

fof(f24904,plain,
    ( spl4_1189
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1189])])).

fof(f23416,plain,
    ( spl4_1103
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1103])])).

fof(f24882,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))))
    | ~ spl4_1103 ),
    inference(superposition,[],[f113,f23418])).

fof(f23418,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | ~ spl4_1103 ),
    inference(avatar_component_clause,[],[f23416])).

fof(f24902,plain,
    ( spl4_1188
    | ~ spl4_1103 ),
    inference(avatar_split_clause,[],[f24881,f23416,f24899])).

fof(f24881,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0))
    | ~ spl4_1103 ),
    inference(superposition,[],[f112,f23418])).

fof(f23598,plain,
    ( spl4_1114
    | ~ spl4_451 ),
    inference(avatar_split_clause,[],[f23597,f5322,f23593])).

fof(f23593,plain,
    ( spl4_1114
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1114])])).

fof(f5322,plain,
    ( spl4_451
  <=> r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_451])])).

fof(f23597,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl4_451 ),
    inference(forward_demodulation,[],[f23589,f81])).

fof(f23589,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)))
    | ~ spl4_451 ),
    inference(resolution,[],[f5324,f114])).

fof(f5324,plain,
    ( r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_451 ),
    inference(avatar_component_clause,[],[f5322])).

fof(f23490,plain,
    ( ~ spl4_1090
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | spl4_425 ),
    inference(avatar_split_clause,[],[f23464,f5188,f1659,f1579,f845,f529,f154,f149,f23188])).

fof(f23188,plain,
    ( spl4_1090
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1090])])).

fof(f23464,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | spl4_425 ),
    inference(unit_resulting_resolution,[],[f156,f5190,f23087,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f23087,plain,
    ( ! [X0] : m1_subset_1(k5_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(unit_resulting_resolution,[],[f22984,f91])).

fof(f22984,plain,
    ( ! [X2] : r1_tarski(k5_xboole_0(X2,k1_xboole_0),X2)
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150 ),
    inference(superposition,[],[f112,f22914])).

fof(f5190,plain,
    ( ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0)
    | spl4_425 ),
    inference(avatar_component_clause,[],[f5188])).

fof(f23419,plain,
    ( spl4_1103
    | ~ spl4_596 ),
    inference(avatar_split_clause,[],[f23400,f12016,f23416])).

fof(f23400,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))
    | ~ spl4_596 ),
    inference(superposition,[],[f113,f12018])).

fof(f23414,plain,
    ( spl4_1053
    | ~ spl4_596 ),
    inference(avatar_split_clause,[],[f23399,f12016,f22580])).

fof(f22580,plain,
    ( spl4_1053
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1053])])).

fof(f23399,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_596 ),
    inference(superposition,[],[f112,f12018])).

fof(f23374,plain,
    ( spl4_451
    | ~ spl4_430 ),
    inference(avatar_split_clause,[],[f23330,f5213,f5322])).

fof(f5213,plain,
    ( spl4_430
  <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_430])])).

fof(f23330,plain,
    ( r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl4_430 ),
    inference(resolution,[],[f5215,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5215,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_430 ),
    inference(avatar_component_clause,[],[f5213])).

fof(f23201,plain,
    ( spl4_596
    | ~ spl4_428 ),
    inference(avatar_split_clause,[],[f23182,f5203,f12016])).

fof(f23182,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl4_428 ),
    inference(resolution,[],[f5205,f115])).

fof(f23186,plain,
    ( spl4_430
    | ~ spl4_4
    | ~ spl4_428 ),
    inference(avatar_split_clause,[],[f23165,f5203,f154,f5213])).

fof(f23165,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_428 ),
    inference(unit_resulting_resolution,[],[f156,f5205,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f23184,plain,
    ( spl4_544
    | ~ spl4_428 ),
    inference(avatar_split_clause,[],[f23169,f5203,f9206])).

fof(f9206,plain,
    ( spl4_544
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_544])])).

fof(f23169,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_428 ),
    inference(unit_resulting_resolution,[],[f5205,f86])).

fof(f23101,plain,
    ( ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | spl4_428 ),
    inference(avatar_contradiction_clause,[],[f23088])).

fof(f23088,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_44
    | ~ spl4_76
    | ~ spl4_144
    | ~ spl4_150
    | spl4_428 ),
    inference(unit_resulting_resolution,[],[f5204,f22984,f91])).

fof(f5204,plain,
    ( ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_428 ),
    inference(avatar_component_clause,[],[f5203])).

fof(f19493,plain,
    ( spl4_989
    | ~ spl4_76
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f19488,f1643,f845,f19490])).

fof(f1643,plain,
    ( spl4_148
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f19488,plain,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,sK1)
    | ~ spl4_76
    | ~ spl4_148 ),
    inference(forward_demodulation,[],[f19419,f1645])).

fof(f1645,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl4_148 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f19419,plain,
    ( k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,sK1)
    | ~ spl4_76 ),
    inference(superposition,[],[f941,f111])).

fof(f111,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f79,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f12577,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f11830,plain,
    ( spl4_410
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_407 ),
    inference(avatar_split_clause,[],[f11795,f5089,f159,f154,f5106])).

fof(f159,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f11795,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_407 ),
    inference(unit_resulting_resolution,[],[f161,f156,f5091,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f161,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f11499,plain,
    ( spl4_525
    | ~ spl4_78
    | ~ spl4_123 ),
    inference(avatar_split_clause,[],[f11498,f1323,f879,f8835])).

fof(f8835,plain,
    ( spl4_525
  <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_525])])).

fof(f879,plain,
    ( spl4_78
  <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f11498,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_78
    | ~ spl4_123 ),
    inference(forward_demodulation,[],[f11487,f881])).

fof(f881,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f879])).

fof(f11487,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_123 ),
    inference(superposition,[],[f113,f1325])).

fof(f11283,plain,
    ( spl4_353
    | ~ spl4_4
    | ~ spl4_319
    | ~ spl4_322 ),
    inference(avatar_split_clause,[],[f11282,f3757,f3711,f154,f4153])).

fof(f4153,plain,
    ( spl4_353
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_353])])).

fof(f3711,plain,
    ( spl4_319
  <=> v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_319])])).

fof(f3757,plain,
    ( spl4_322
  <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).

fof(f11282,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_4
    | ~ spl4_319
    | ~ spl4_322 ),
    inference(subsumption_resolution,[],[f11281,f156])).

fof(f11281,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_319
    | ~ spl4_322 ),
    inference(subsumption_resolution,[],[f11246,f3713])).

fof(f3713,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl4_319 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f11246,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_322 ),
    inference(resolution,[],[f3759,f75])).

fof(f3759,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_322 ),
    inference(avatar_component_clause,[],[f3757])).

fof(f11197,plain,
    ( spl4_322
    | ~ spl4_135
    | ~ spl4_310 ),
    inference(avatar_split_clause,[],[f11196,f3649,f1456,f3757])).

fof(f1456,plain,
    ( spl4_135
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f3649,plain,
    ( spl4_310
  <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f11196,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_135
    | ~ spl4_310 ),
    inference(forward_demodulation,[],[f1458,f3651])).

fof(f3651,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_310 ),
    inference(avatar_component_clause,[],[f3649])).

fof(f1458,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f11062,plain,
    ( sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | k1_xboole_0 != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1)
    | sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))
    | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f10845,plain,
    ( spl4_193
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f10844,f1328,f2393])).

fof(f2393,plain,
    ( spl4_193
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).

fof(f1328,plain,
    ( spl4_124
  <=> r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f10844,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_124 ),
    inference(forward_demodulation,[],[f10840,f81])).

fof(f10840,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)))
    | ~ spl4_124 ),
    inference(resolution,[],[f1330,f114])).

fof(f1330,plain,
    ( r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f10761,plain,
    ( spl4_135
    | ~ spl4_4
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f10739,f689,f154,f1456])).

fof(f689,plain,
    ( spl4_57
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f10739,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_57 ),
    inference(unit_resulting_resolution,[],[f156,f691,f89])).

fof(f691,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f689])).

fof(f10733,plain,
    ( spl4_123
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f10732,f765,f704,f1323])).

fof(f704,plain,
    ( spl4_60
  <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f765,plain,
    ( spl4_68
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f10732,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))))
    | ~ spl4_60
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f10701,f767])).

fof(f767,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f765])).

fof(f10701,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))))
    | ~ spl4_60 ),
    inference(resolution,[],[f706,f115])).

fof(f706,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f704])).

fof(f10731,plain,
    ( spl4_124
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f10700,f704,f1328])).

fof(f10700,plain,
    ( r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_60 ),
    inference(resolution,[],[f706,f90])).

fof(f10672,plain,
    ( spl4_75
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f10671,f699,f834])).

fof(f699,plain,
    ( spl4_59
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f10671,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f10668,f81])).

fof(f10668,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)))
    | ~ spl4_59 ),
    inference(resolution,[],[f701,f114])).

fof(f701,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f699])).

fof(f9410,plain,
    ( spl4_107
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f9384,f318,f1141])).

fof(f1141,plain,
    ( spl4_107
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f318,plain,
    ( spl4_19
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f9384,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ spl4_19 ),
    inference(resolution,[],[f320,f115])).

fof(f320,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f318])).

fof(f9294,plain,
    ( spl4_45
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f9293,f328,f543])).

fof(f543,plain,
    ( spl4_45
  <=> k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f328,plain,
    ( spl4_21
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f9293,plain,
    ( k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f9289,f81])).

fof(f9289,plain,
    ( k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(resolution,[],[f330,f114])).

fof(f330,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f328])).

fof(f9277,plain,
    ( spl4_20
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f9251,f216,f323])).

fof(f323,plain,
    ( spl4_20
  <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f9251,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_9 ),
    inference(resolution,[],[f218,f115])).

fof(f9276,plain,
    ( spl4_21
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f9250,f216,f328])).

fof(f9250,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f218,f90])).

fof(f9254,plain,
    ( spl4_19
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f9238,f216,f318])).

fof(f9238,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f218,f86])).

fof(f8267,plain,
    ( spl4_90
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f8232,f236,f149,f970])).

fof(f970,plain,
    ( spl4_90
  <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f236,plain,
    ( spl4_13
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f8232,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f815,f238])).

fof(f238,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f236])).

fof(f815,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f810,f81])).

fof(f810,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f507,f114])).

fof(f507,plain,
    ( ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f112,f181])).

fof(f8224,plain,
    ( spl4_369
    | ~ spl4_3
    | ~ spl4_368 ),
    inference(avatar_split_clause,[],[f8219,f4435,f149,f4449])).

fof(f4449,plain,
    ( spl4_369
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_369])])).

fof(f8219,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_368 ),
    inference(superposition,[],[f533,f4437])).

fof(f533,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f500,f181])).

fof(f500,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))))
    | ~ spl4_3 ),
    inference(superposition,[],[f181,f113])).

fof(f7830,plain,
    ( spl4_363
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_358 ),
    inference(avatar_split_clause,[],[f7829,f4309,f236,f149,f4385])).

fof(f4385,plain,
    ( spl4_363
  <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_363])])).

fof(f7829,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_358 ),
    inference(forward_demodulation,[],[f7806,f238])).

fof(f7806,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_358 ),
    inference(superposition,[],[f181,f4311])).

fof(f7116,plain,
    ( spl4_224
    | ~ spl4_117 ),
    inference(avatar_split_clause,[],[f7112,f1212,f2701])).

fof(f2701,plain,
    ( spl4_224
  <=> k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f1212,plain,
    ( spl4_117
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f7112,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))))
    | ~ spl4_117 ),
    inference(resolution,[],[f1214,f115])).

fof(f1214,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_117 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f6749,plain,
    ( spl4_237
    | ~ spl4_225 ),
    inference(avatar_split_clause,[],[f6748,f2706,f2814])).

fof(f2814,plain,
    ( spl4_237
  <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_237])])).

fof(f2706,plain,
    ( spl4_225
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_225])])).

fof(f6748,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl4_225 ),
    inference(forward_demodulation,[],[f6744,f81])).

fof(f6744,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1))
    | ~ spl4_225 ),
    inference(resolution,[],[f2708,f114])).

fof(f2708,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl4_225 ),
    inference(avatar_component_clause,[],[f2706])).

fof(f6663,plain,
    ( spl4_145
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f6655,f236,f149,f1584])).

fof(f1584,plain,
    ( spl4_145
  <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).

fof(f6655,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f533,f238])).

fof(f6587,plain,
    ( spl4_358
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f6583,f236,f149,f4309])).

fof(f6583,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f4260,f238])).

fof(f4260,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f508,f815])).

fof(f508,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))))
    | ~ spl4_3 ),
    inference(superposition,[],[f113,f181])).

fof(f6437,plain,
    ( spl4_57
    | ~ spl4_30
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f6436,f590,f410,f689])).

fof(f410,plain,
    ( spl4_30
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f590,plain,
    ( spl4_47
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f6436,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f412,f592])).

fof(f592,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f590])).

fof(f412,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f410])).

fof(f6255,plain,
    ( spl4_60
    | ~ spl4_33
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f6254,f590,f425,f704])).

fof(f425,plain,
    ( spl4_33
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f6254,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_33
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f427,f592])).

fof(f427,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f425])).

fof(f6144,plain,
    ( spl4_61
    | ~ spl4_34
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f6143,f590,f430,f709])).

fof(f709,plain,
    ( spl4_61
  <=> v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f430,plain,
    ( spl4_34
  <=> v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f6143,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_34
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f432,f592])).

fof(f432,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f430])).

fof(f6142,plain,
    ( spl4_78
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f6119,f783,f879])).

fof(f783,plain,
    ( spl4_70
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f6119,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl4_70 ),
    inference(resolution,[],[f785,f115])).

fof(f785,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f783])).

fof(f6138,plain,
    ( spl4_82
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f6137,f783,f154,f899])).

fof(f899,plain,
    ( spl4_82
  <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f6137,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f6110,f156])).

fof(f6110,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_70 ),
    inference(resolution,[],[f785,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f6136,plain,
    ( spl4_83
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f6135,f783,f154,f904])).

fof(f904,plain,
    ( spl4_83
  <=> k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f6135,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f6109,f156])).

fof(f6109,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_70 ),
    inference(resolution,[],[f785,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f6070,plain,
    ( spl4_118
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f6066,f975,f1217])).

fof(f1217,plain,
    ( spl4_118
  <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f975,plain,
    ( spl4_91
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f6066,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl4_91 ),
    inference(resolution,[],[f977,f115])).

fof(f977,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f975])).

fof(f6068,plain,
    ( spl4_117
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f6063,f975,f1212])).

fof(f6063,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_91 ),
    inference(unit_resulting_resolution,[],[f977,f86])).

fof(f6036,plain,
    ( spl4_59
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f6035,f590,f420,f699])).

fof(f420,plain,
    ( spl4_32
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f6035,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f422,f592])).

fof(f422,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f420])).

fof(f5968,plain,
    ( ~ spl4_60
    | spl4_70
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f5964,f765,f783,f704])).

fof(f5964,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_68 ),
    inference(superposition,[],[f86,f767])).

fof(f5958,plain,
    ( spl4_68
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f5957,f590,f231,f765])).

fof(f231,plain,
    ( spl4_12
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f5957,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f233,f592])).

fof(f233,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f231])).

fof(f5944,plain,
    ( spl4_91
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f5938,f818,f975])).

fof(f818,plain,
    ( spl4_73
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f5938,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_73 ),
    inference(unit_resulting_resolution,[],[f820,f91])).

fof(f820,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f818])).

fof(f5936,plain,
    ( spl4_44
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f5919,f149,f529])).

fof(f5919,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f110,f181])).

fof(f5933,plain,
    ( spl4_43
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f5907,f149,f524])).

fof(f524,plain,
    ( spl4_43
  <=> k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f5907,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f181,f111])).

fof(f5805,plain,
    ( spl4_31
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5780,f200,f415])).

fof(f415,plain,
    ( spl4_31
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f200,plain,
    ( spl4_6
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f5780,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f115])).

fof(f202,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f5804,plain,
    ( spl4_32
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5779,f200,f420])).

fof(f5779,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f90])).

fof(f5800,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5799,f200,f154,f468,f464])).

fof(f464,plain,
    ( spl4_39
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f468,plain,
    ( spl4_40
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f5799,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f5772,f156])).

fof(f5772,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f75])).

fof(f5796,plain,
    ( spl4_36
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5795,f200,f154,f440])).

fof(f440,plain,
    ( spl4_36
  <=> k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f5795,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f5770,f156])).

fof(f5770,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f73])).

fof(f5792,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5791,f200,f154,f450])).

fof(f450,plain,
    ( spl4_38
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f5791,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f5768,f156])).

fof(f5768,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f5786,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5762,f200,f159,f154,f430])).

fof(f5762,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f161,f156,f202,f88])).

fof(f5785,plain,
    ( spl4_33
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5763,f200,f154,f425])).

fof(f5763,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f156,f202,f89])).

fof(f5782,plain,
    ( spl4_30
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f5767,f200,f410])).

fof(f5767,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f202,f86])).

fof(f5700,plain,
    ( spl4_18
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f5698,f211,f285])).

fof(f211,plain,
    ( spl4_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f5698,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(resolution,[],[f213,f114])).

fof(f213,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f5694,plain,
    ( spl4_76
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f5690,f824,f845])).

fof(f824,plain,
    ( spl4_74
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f5690,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_74 ),
    inference(unit_resulting_resolution,[],[f826,f91])).

fof(f826,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f824])).

fof(f5682,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f5681,f149,f206])).

fof(f206,plain,
    ( spl4_7
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f5681,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f5655,f81])).

fof(f5655,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f151,f115])).

fof(f5680,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f5654,f149,f211])).

fof(f5654,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f151,f90])).

fof(f5672,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5671,f154,f149,f231])).

fof(f5671,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f5645,f156])).

fof(f5645,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f151,f73])).

fof(f5670,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5669,f154,f149,f236])).

fof(f5669,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f5644,f156])).

fof(f5644,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f151,f72])).

fof(f5668,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5667,f154,f149,f241])).

fof(f241,plain,
    ( spl4_14
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f5667,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f5643,f156])).

fof(f5643,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f151,f71])).

fof(f5662,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f5637,f159,f154,f149,f221])).

fof(f221,plain,
    ( spl4_10
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f5637,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f161,f156,f151,f88])).

fof(f5661,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5638,f154,f149,f216])).

fof(f5638,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f156,f151,f89])).

fof(f5657,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f5642,f149,f200])).

fof(f5642,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f151,f86])).

fof(f4438,plain,
    ( spl4_368
    | ~ spl4_145
    | ~ spl4_358 ),
    inference(avatar_split_clause,[],[f4433,f4309,f1584,f4435])).

fof(f4433,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_145
    | ~ spl4_358 ),
    inference(forward_demodulation,[],[f1586,f4311])).

fof(f1586,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_145 ),
    inference(avatar_component_clause,[],[f1584])).

fof(f3714,plain,
    ( spl4_319
    | ~ spl4_165
    | ~ spl4_310 ),
    inference(avatar_split_clause,[],[f3673,f3649,f1921,f3711])).

fof(f1921,plain,
    ( spl4_165
  <=> v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_165])])).

fof(f3673,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl4_165
    | ~ spl4_310 ),
    inference(backward_demodulation,[],[f1923,f3651])).

fof(f1923,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl4_165 ),
    inference(avatar_component_clause,[],[f1921])).

fof(f3652,plain,
    ( spl4_310
    | ~ spl4_58
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f3622,f834,f694,f3649])).

fof(f694,plain,
    ( spl4_58
  <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f3622,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_58
    | ~ spl4_75 ),
    inference(backward_demodulation,[],[f696,f836])).

fof(f696,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f694])).

fof(f2710,plain,
    ( spl4_225
    | ~ spl4_117 ),
    inference(avatar_split_clause,[],[f2692,f1212,f2706])).

fof(f2692,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl4_117 ),
    inference(resolution,[],[f1214,f90])).

fof(f1946,plain,
    ( spl4_167
    | ~ spl4_162 ),
    inference(avatar_split_clause,[],[f1945,f1849,f1936])).

fof(f1849,plain,
    ( spl4_162
  <=> r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f1945,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_162 ),
    inference(forward_demodulation,[],[f1933,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1933,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0))
    | ~ spl4_162 ),
    inference(resolution,[],[f1851,f114])).

fof(f1851,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_162 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1924,plain,
    ( ~ spl4_135
    | spl4_165
    | ~ spl4_4
    | ~ spl4_61
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f1919,f719,f709,f154,f1921,f1456])).

fof(f719,plain,
    ( spl4_63
  <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f1919,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_61
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f1918,f156])).

fof(f1918,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_61
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f1914,f711])).

fof(f711,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f709])).

fof(f1914,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0)
    | v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_63 ),
    inference(superposition,[],[f78,f721])).

fof(f721,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f719])).

fof(f1887,plain,
    ( spl4_164
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f1874,f694,f1884])).

fof(f1884,plain,
    ( spl4_164
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f1874,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))))
    | ~ spl4_58 ),
    inference(superposition,[],[f113,f696])).

fof(f1864,plain,
    ( spl4_63
    | ~ spl4_36
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f1863,f590,f440,f719])).

fof(f1863,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_36
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f442,f592])).

fof(f442,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f440])).

fof(f1852,plain,
    ( spl4_162
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f1827,f1659,f1849])).

fof(f1827,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_150 ),
    inference(superposition,[],[f112,f1661])).

fof(f1821,plain,
    ( spl4_58
    | ~ spl4_31
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f1820,f590,f415,f694])).

fof(f1820,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_31
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f417,f592])).

fof(f417,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f415])).

fof(f1734,plain,
    ( spl4_156
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f1721,f323,f1731])).

fof(f1731,plain,
    ( spl4_156
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f1721,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ spl4_20 ),
    inference(superposition,[],[f113,f325])).

fof(f325,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f323])).

fof(f1668,plain,
    ( spl4_150
    | ~ spl4_147 ),
    inference(avatar_split_clause,[],[f1657,f1610,f1659])).

fof(f1610,plain,
    ( spl4_147
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).

fof(f1657,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))
    | ~ spl4_147 ),
    inference(resolution,[],[f1612,f114])).

fof(f1612,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_147 ),
    inference(avatar_component_clause,[],[f1610])).

fof(f1653,plain,
    ( spl4_50
    | ~ spl4_3
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f1652,f524,f149,f605])).

fof(f605,plain,
    ( spl4_50
  <=> sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1652,plain,
    ( sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl4_3
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f1617,f111])).

fof(f1617,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl4_3
    | ~ spl4_43 ),
    inference(superposition,[],[f508,f526])).

fof(f526,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1646,plain,
    ( spl4_148
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1641,f529,f149,f1643])).

fof(f1641,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1640,f109])).

fof(f1640,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1614,f111])).

fof(f1614,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1)))
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(superposition,[],[f508,f531])).

fof(f1613,plain,
    ( spl4_147
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f1601,f149,f1610])).

fof(f1601,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f1576,f109])).

fof(f1576,plain,
    ( ! [X4] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X4)),sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f507,f533])).

fof(f1582,plain,
    ( spl4_144
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1577,f529,f149,f1579])).

fof(f1577,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1569,f109])).

fof(f1569,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(superposition,[],[f533,f531])).

fof(f827,plain,
    ( spl4_74
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f822,f529,f149,f824])).

fof(f822,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(superposition,[],[f507,f531])).

fof(f821,plain,
    ( spl4_73
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f813,f236,f149,f818])).

fof(f813,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f507,f238])).

fof(f806,plain,
    ( spl4_72
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f794,f658,f802])).

fof(f802,plain,
    ( spl4_72
  <=> k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f658,plain,
    ( spl4_56
  <=> m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f794,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl4_56 ),
    inference(resolution,[],[f660,f115])).

fof(f660,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f658])).

fof(f661,plain,
    ( spl4_56
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f647,f600,f658])).

fof(f600,plain,
    ( spl4_49
  <=> r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f647,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_49 ),
    inference(unit_resulting_resolution,[],[f602,f91])).

fof(f602,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f600])).

fof(f603,plain,
    ( spl4_49
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f569,f285,f600])).

fof(f569,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl4_18 ),
    inference(superposition,[],[f112,f287])).

fof(f593,plain,
    ( spl4_47
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f564,f285,f206,f590])).

fof(f564,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f208,f287])).

fof(f208,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f206])).

fof(f558,plain,
    ( ~ spl4_46
    | ~ spl4_4
    | ~ spl4_6
    | spl4_39 ),
    inference(avatar_split_clause,[],[f549,f464,f200,f154,f555])).

fof(f555,plain,
    ( spl4_46
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f549,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_6
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f156,f202,f466,f78])).

fof(f466,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f464])).

fof(f162,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f64,f159])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f157,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f65,f154])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f152,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f66,f149])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f67,f143,f139])).

fof(f139,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f146,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f68,f143,f139])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:40 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.50  % (12259)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12257)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (12260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (12240)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (12239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (12259)Refutation not found, incomplete strategy% (12259)------------------------------
% 0.20/0.51  % (12259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12259)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12259)Memory used [KB]: 10746
% 0.20/0.51  % (12259)Time elapsed: 0.065 s
% 0.20/0.51  % (12259)------------------------------
% 0.20/0.51  % (12259)------------------------------
% 0.20/0.51  % (12251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (12237)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (12238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12234)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (12235)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (12245)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (12262)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (12252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (12236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (12250)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (12264)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (12254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (12265)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (12254)Refutation not found, incomplete strategy% (12254)------------------------------
% 0.20/0.54  % (12254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12254)Memory used [KB]: 10618
% 0.20/0.54  % (12254)Time elapsed: 0.139 s
% 0.20/0.54  % (12254)------------------------------
% 0.20/0.54  % (12254)------------------------------
% 0.20/0.54  % (12266)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (12258)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (12255)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (12248)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (12242)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (12243)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12263)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (12256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (12249)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (12244)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.57  % (12261)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.19/0.68  % (12274)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.69  % (12273)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.16/0.81  % (12239)Time limit reached!
% 3.16/0.81  % (12239)------------------------------
% 3.16/0.81  % (12239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.81  % (12239)Termination reason: Time limit
% 3.16/0.81  
% 3.16/0.81  % (12239)Memory used [KB]: 8827
% 3.16/0.81  % (12239)Time elapsed: 0.408 s
% 3.16/0.81  % (12239)------------------------------
% 3.16/0.81  % (12239)------------------------------
% 4.01/0.92  % (12244)Time limit reached!
% 4.01/0.92  % (12244)------------------------------
% 4.01/0.92  % (12244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (12244)Termination reason: Time limit
% 4.01/0.92  
% 4.01/0.92  % (12244)Memory used [KB]: 12537
% 4.01/0.92  % (12244)Time elapsed: 0.519 s
% 4.01/0.92  % (12244)------------------------------
% 4.01/0.92  % (12244)------------------------------
% 4.01/0.92  % (12248)Time limit reached!
% 4.01/0.92  % (12248)------------------------------
% 4.01/0.92  % (12248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (12248)Termination reason: Time limit
% 4.01/0.92  
% 4.01/0.92  % (12248)Memory used [KB]: 9850
% 4.01/0.92  % (12248)Time elapsed: 0.522 s
% 4.01/0.92  % (12248)------------------------------
% 4.01/0.92  % (12248)------------------------------
% 4.35/0.92  % (12235)Time limit reached!
% 4.35/0.92  % (12235)------------------------------
% 4.35/0.92  % (12235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.92  % (12235)Termination reason: Time limit
% 4.35/0.92  
% 4.35/0.92  % (12235)Memory used [KB]: 9466
% 4.35/0.92  % (12235)Time elapsed: 0.518 s
% 4.35/0.92  % (12235)------------------------------
% 4.35/0.92  % (12235)------------------------------
% 4.35/0.94  % (12321)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.35/0.95  % (12234)Time limit reached!
% 4.35/0.95  % (12234)------------------------------
% 4.35/0.95  % (12234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.96  % (12234)Termination reason: Time limit
% 4.52/0.96  
% 4.52/0.96  % (12234)Memory used [KB]: 5500
% 4.52/0.96  % (12234)Time elapsed: 0.537 s
% 4.52/0.96  % (12234)------------------------------
% 4.52/0.96  % (12234)------------------------------
% 4.52/1.01  % (12241)Time limit reached!
% 4.52/1.01  % (12241)------------------------------
% 4.52/1.01  % (12241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.01  % (12241)Termination reason: Time limit
% 4.52/1.01  
% 4.52/1.01  % (12241)Memory used [KB]: 11641
% 4.52/1.01  % (12241)Time elapsed: 0.602 s
% 4.52/1.01  % (12241)------------------------------
% 4.52/1.01  % (12241)------------------------------
% 4.52/1.01  % (12265)Time limit reached!
% 4.52/1.01  % (12265)------------------------------
% 4.52/1.01  % (12265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.01  % (12265)Termination reason: Time limit
% 4.52/1.01  
% 4.52/1.01  % (12265)Memory used [KB]: 9210
% 4.52/1.01  % (12265)Time elapsed: 0.610 s
% 4.52/1.01  % (12265)------------------------------
% 4.52/1.01  % (12265)------------------------------
% 4.52/1.02  % (12252)Time limit reached!
% 4.52/1.02  % (12252)------------------------------
% 4.52/1.02  % (12252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.03  % (12390)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.03/1.03  % (12252)Termination reason: Time limit
% 5.03/1.03  % (12252)Termination phase: Saturation
% 5.03/1.03  
% 5.03/1.03  % (12252)Memory used [KB]: 16502
% 5.03/1.03  % (12252)Time elapsed: 0.600 s
% 5.03/1.03  % (12252)------------------------------
% 5.03/1.03  % (12252)------------------------------
% 5.03/1.04  % (12387)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.03/1.05  % (12389)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.62/1.08  % (12412)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.62/1.13  % (12450)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.62/1.15  % (12441)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.62/1.15  % (12443)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.46/1.20  % (12258)Time limit reached!
% 6.46/1.20  % (12258)------------------------------
% 6.46/1.20  % (12258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.46/1.20  % (12258)Termination reason: Time limit
% 6.46/1.20  % (12258)Termination phase: Saturation
% 6.46/1.20  
% 6.46/1.21  % (12258)Memory used [KB]: 8699
% 6.46/1.21  % (12258)Time elapsed: 0.800 s
% 6.46/1.21  % (12258)------------------------------
% 6.46/1.21  % (12258)------------------------------
% 7.44/1.35  % (12387)Time limit reached!
% 7.44/1.35  % (12387)------------------------------
% 7.44/1.35  % (12387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.44/1.36  % (12387)Termination reason: Time limit
% 7.44/1.36  % (12387)Termination phase: Saturation
% 7.44/1.36  
% 7.44/1.36  % (12387)Memory used [KB]: 7675
% 7.44/1.36  % (12387)Time elapsed: 0.400 s
% 7.44/1.36  % (12387)------------------------------
% 7.44/1.36  % (12387)------------------------------
% 7.44/1.36  % (12497)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.90/1.37  % (12389)Time limit reached!
% 7.90/1.37  % (12389)------------------------------
% 7.90/1.37  % (12389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.90/1.37  % (12389)Termination reason: Time limit
% 7.90/1.37  
% 7.90/1.37  % (12389)Memory used [KB]: 13944
% 7.90/1.37  % (12389)Time elapsed: 0.426 s
% 7.90/1.37  % (12389)------------------------------
% 7.90/1.37  % (12389)------------------------------
% 7.90/1.42  % (12236)Time limit reached!
% 7.90/1.42  % (12236)------------------------------
% 7.90/1.42  % (12236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.90/1.43  % (12236)Termination reason: Time limit
% 7.90/1.43  % (12236)Termination phase: Saturation
% 7.90/1.43  
% 7.90/1.43  % (12236)Memory used [KB]: 21748
% 7.90/1.43  % (12236)Time elapsed: 1.0000 s
% 7.90/1.43  % (12236)------------------------------
% 7.90/1.43  % (12236)------------------------------
% 8.56/1.48  % (12525)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.75/1.51  % (12526)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.13/1.54  % (12527)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.91/1.62  % (12263)Time limit reached!
% 9.91/1.62  % (12263)------------------------------
% 9.91/1.62  % (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.91/1.63  % (12263)Termination reason: Time limit
% 9.91/1.63  
% 9.91/1.63  % (12263)Memory used [KB]: 19061
% 9.91/1.63  % (12263)Time elapsed: 1.216 s
% 9.91/1.63  % (12263)------------------------------
% 9.91/1.63  % (12263)------------------------------
% 10.35/1.71  % (12251)Time limit reached!
% 10.35/1.71  % (12251)------------------------------
% 10.35/1.71  % (12251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.71  % (12251)Termination reason: Time limit
% 10.35/1.71  
% 10.35/1.71  % (12251)Memory used [KB]: 20724
% 10.35/1.71  % (12251)Time elapsed: 1.308 s
% 10.35/1.71  % (12251)------------------------------
% 10.35/1.71  % (12251)------------------------------
% 10.35/1.73  % (12261)Time limit reached!
% 10.35/1.73  % (12261)------------------------------
% 10.35/1.73  % (12261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.73  % (12261)Termination reason: Time limit
% 10.35/1.73  
% 10.35/1.73  % (12261)Memory used [KB]: 22003
% 10.35/1.73  % (12261)Time elapsed: 1.323 s
% 10.35/1.73  % (12261)------------------------------
% 10.35/1.73  % (12261)------------------------------
% 10.35/1.73  % (12528)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.52/1.85  % (12529)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.52/1.86  % (12530)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.52/1.89  % (12526)Time limit reached!
% 11.52/1.89  % (12526)------------------------------
% 11.52/1.89  % (12526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.52/1.90  % (12526)Termination reason: Time limit
% 11.52/1.90  
% 11.52/1.90  % (12526)Memory used [KB]: 2814
% 11.52/1.90  % (12526)Time elapsed: 0.504 s
% 11.52/1.90  % (12526)------------------------------
% 11.52/1.90  % (12526)------------------------------
% 12.12/1.92  % (12238)Time limit reached!
% 12.12/1.92  % (12238)------------------------------
% 12.12/1.92  % (12238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.92  % (12238)Termination reason: Time limit
% 12.12/1.92  % (12238)Termination phase: Saturation
% 12.12/1.92  
% 12.12/1.92  % (12238)Memory used [KB]: 14456
% 12.12/1.92  % (12238)Time elapsed: 1.515 s
% 12.12/1.92  % (12238)------------------------------
% 12.12/1.92  % (12238)------------------------------
% 12.12/1.92  % (12264)Time limit reached!
% 12.12/1.92  % (12264)------------------------------
% 12.12/1.92  % (12264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.94  % (12264)Termination reason: Time limit
% 12.12/1.94  % (12264)Termination phase: Saturation
% 12.12/1.94  
% 12.12/1.94  % (12264)Memory used [KB]: 16502
% 12.12/1.94  % (12264)Time elapsed: 1.500 s
% 12.12/1.94  % (12264)------------------------------
% 12.12/1.94  % (12264)------------------------------
% 12.60/2.02  % (12245)Time limit reached!
% 12.60/2.02  % (12245)------------------------------
% 12.60/2.02  % (12245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.60/2.02  % (12245)Termination reason: Time limit
% 12.60/2.02  
% 12.60/2.02  % (12245)Memory used [KB]: 15735
% 12.60/2.02  % (12245)Time elapsed: 1.626 s
% 12.60/2.02  % (12245)------------------------------
% 12.60/2.02  % (12245)------------------------------
% 12.60/2.03  % (12531)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.60/2.04  % (12532)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.60/2.05  % (12533)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 14.03/2.16  % (12534)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.03/2.19  % (12530)Time limit reached!
% 14.03/2.19  % (12530)------------------------------
% 14.03/2.19  % (12530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.03/2.19  % (12530)Termination reason: Time limit
% 14.03/2.19  
% 14.03/2.19  % (12530)Memory used [KB]: 4477
% 14.03/2.19  % (12530)Time elapsed: 0.427 s
% 14.03/2.19  % (12530)------------------------------
% 14.03/2.19  % (12530)------------------------------
% 14.03/2.21  % (12412)Time limit reached!
% 14.03/2.21  % (12412)------------------------------
% 14.03/2.21  % (12412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.03/2.21  % (12412)Termination reason: Time limit
% 14.03/2.21  
% 14.03/2.21  % (12412)Memory used [KB]: 12409
% 14.03/2.21  % (12412)Time elapsed: 1.223 s
% 14.03/2.21  % (12412)------------------------------
% 14.03/2.21  % (12412)------------------------------
% 14.03/2.21  % (12250)Time limit reached!
% 14.03/2.21  % (12250)------------------------------
% 14.03/2.21  % (12250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.72/2.22  % (12250)Termination reason: Time limit
% 14.72/2.22  
% 14.72/2.22  % (12250)Memory used [KB]: 8443
% 14.72/2.22  % (12250)Time elapsed: 1.816 s
% 14.72/2.22  % (12250)------------------------------
% 14.72/2.22  % (12250)------------------------------
% 15.22/2.30  % (12535)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.22/2.31  % (12536)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.22/2.35  % (12537)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.85/2.40  % (12533)Time limit reached!
% 15.85/2.40  % (12533)------------------------------
% 15.85/2.40  % (12533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.85/2.40  % (12533)Termination reason: Time limit
% 15.85/2.40  
% 15.85/2.40  % (12533)Memory used [KB]: 3326
% 15.85/2.40  % (12533)Time elapsed: 0.408 s
% 15.85/2.40  % (12533)------------------------------
% 15.85/2.40  % (12533)------------------------------
% 16.21/2.43  % (12255)Time limit reached!
% 16.21/2.43  % (12255)------------------------------
% 16.21/2.43  % (12255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.21/2.44  % (12255)Termination reason: Time limit
% 16.21/2.44  % (12255)Termination phase: Saturation
% 16.21/2.44  
% 16.21/2.44  % (12255)Memory used [KB]: 20724
% 16.21/2.44  % (12255)Time elapsed: 2.0000 s
% 16.21/2.44  % (12255)------------------------------
% 16.21/2.44  % (12255)------------------------------
% 16.85/2.54  % (12538)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.85/2.54  % (12240)Time limit reached!
% 16.85/2.54  % (12240)------------------------------
% 16.85/2.54  % (12240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.85/2.54  % (12240)Termination reason: Time limit
% 16.85/2.54  
% 16.85/2.54  % (12240)Memory used [KB]: 29040
% 16.85/2.54  % (12240)Time elapsed: 2.074 s
% 16.85/2.54  % (12240)------------------------------
% 16.85/2.54  % (12240)------------------------------
% 16.85/2.55  % (12321)Time limit reached!
% 16.85/2.55  % (12321)------------------------------
% 16.85/2.55  % (12321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.85/2.57  % (12539)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.85/2.58  % (12321)Termination reason: Time limit
% 16.85/2.58  
% 16.85/2.58  % (12321)Memory used [KB]: 23794
% 16.85/2.58  % (12321)Time elapsed: 1.720 s
% 16.85/2.58  % (12321)------------------------------
% 16.85/2.58  % (12321)------------------------------
% 17.81/2.67  % (12540)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.87/2.71  % (12541)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 18.83/2.74  % (12443)Time limit reached!
% 18.83/2.74  % (12443)------------------------------
% 18.83/2.74  % (12443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.83/2.76  % (12443)Termination reason: Time limit
% 18.83/2.76  
% 18.83/2.76  % (12443)Memory used [KB]: 13560
% 18.83/2.76  % (12443)Time elapsed: 1.714 s
% 18.83/2.76  % (12443)------------------------------
% 18.83/2.76  % (12443)------------------------------
% 19.59/2.87  % (12538)Time limit reached!
% 19.59/2.87  % (12538)------------------------------
% 19.59/2.87  % (12538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.59/2.87  % (12538)Termination reason: Time limit
% 19.59/2.87  % (12538)Termination phase: Saturation
% 19.59/2.87  
% 19.59/2.87  % (12538)Memory used [KB]: 9978
% 19.59/2.87  % (12538)Time elapsed: 0.400 s
% 19.59/2.87  % (12538)------------------------------
% 19.59/2.87  % (12538)------------------------------
% 20.68/2.97  % (12529)Time limit reached!
% 20.68/2.97  % (12529)------------------------------
% 20.68/2.97  % (12529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.68/2.97  % (12529)Termination reason: Time limit
% 20.68/2.97  
% 20.68/2.97  % (12529)Memory used [KB]: 13304
% 20.68/2.97  % (12529)Time elapsed: 1.205 s
% 20.68/2.97  % (12529)------------------------------
% 20.68/2.97  % (12529)------------------------------
% 20.68/2.98  % (12540)Time limit reached!
% 20.68/2.98  % (12540)------------------------------
% 20.68/2.98  % (12540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.68/2.98  % (12242)Time limit reached!
% 20.68/2.98  % (12242)------------------------------
% 20.68/2.98  % (12242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.68/2.98  % (12540)Termination reason: Time limit
% 20.68/2.98  % (12540)Termination phase: Saturation
% 20.68/2.98  
% 20.68/2.98  % (12540)Memory used [KB]: 10618
% 20.68/2.98  % (12540)Time elapsed: 0.400 s
% 20.68/2.98  % (12540)------------------------------
% 20.68/2.98  % (12540)------------------------------
% 20.68/3.00  % (12242)Termination reason: Time limit
% 20.68/3.00  
% 20.68/3.00  % (12242)Memory used [KB]: 33517
% 20.68/3.00  % (12242)Time elapsed: 2.584 s
% 20.68/3.00  % (12242)------------------------------
% 20.68/3.00  % (12242)------------------------------
% 20.68/3.00  % (12256)Time limit reached!
% 20.68/3.00  % (12256)------------------------------
% 20.68/3.00  % (12256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.68/3.00  % (12256)Termination reason: Time limit
% 20.68/3.00  
% 20.68/3.00  % (12256)Memory used [KB]: 40425
% 20.68/3.00  % (12256)Time elapsed: 2.608 s
% 20.68/3.00  % (12256)------------------------------
% 20.68/3.00  % (12256)------------------------------
% 23.07/3.27  % (12532)Time limit reached!
% 23.07/3.27  % (12532)------------------------------
% 23.07/3.27  % (12532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.18/3.28  % (12532)Termination reason: Time limit
% 23.18/3.28  % (12532)Termination phase: Saturation
% 23.18/3.28  
% 23.18/3.28  % (12532)Memory used [KB]: 8699
% 23.18/3.28  % (12532)Time elapsed: 1.300 s
% 23.18/3.28  % (12532)------------------------------
% 23.18/3.28  % (12532)------------------------------
% 23.76/3.40  % (12249)Time limit reached!
% 23.76/3.40  % (12249)------------------------------
% 23.76/3.40  % (12249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.76/3.40  % (12249)Termination reason: Time limit
% 23.76/3.40  
% 23.76/3.40  % (12249)Memory used [KB]: 14711
% 23.76/3.40  % (12249)Time elapsed: 3.004 s
% 23.76/3.40  % (12249)------------------------------
% 23.76/3.40  % (12249)------------------------------
% 23.76/3.41  % (12274)Time limit reached!
% 23.76/3.41  % (12274)------------------------------
% 23.76/3.41  % (12274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.76/3.41  % (12274)Termination reason: Time limit
% 23.76/3.41  
% 23.76/3.41  % (12274)Memory used [KB]: 31342
% 23.76/3.41  % (12274)Time elapsed: 2.823 s
% 23.76/3.41  % (12274)------------------------------
% 23.76/3.41  % (12274)------------------------------
% 30.93/4.30  % (12266)Time limit reached!
% 30.93/4.30  % (12266)------------------------------
% 30.93/4.30  % (12266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.93/4.31  % (12266)Termination reason: Time limit
% 30.93/4.31  % (12266)Termination phase: Saturation
% 30.93/4.31  
% 30.93/4.31  % (12266)Memory used [KB]: 34029
% 30.93/4.31  % (12266)Time elapsed: 3.900 s
% 30.93/4.31  % (12266)------------------------------
% 30.93/4.31  % (12266)------------------------------
% 31.56/4.33  % (12262)Refutation found. Thanks to Tanya!
% 31.56/4.33  % SZS status Theorem for theBenchmark
% 31.56/4.34  % SZS output start Proof for theBenchmark
% 31.56/4.35  fof(f46931,plain,(
% 31.56/4.35    $false),
% 31.56/4.35    inference(avatar_sat_refutation,[],[f146,f147,f152,f157,f162,f558,f593,f603,f661,f806,f821,f827,f1582,f1613,f1646,f1653,f1668,f1734,f1821,f1852,f1864,f1887,f1924,f1946,f2710,f3652,f3714,f4438,f5657,f5661,f5662,f5668,f5670,f5672,f5680,f5682,f5694,f5700,f5782,f5785,f5786,f5792,f5796,f5800,f5804,f5805,f5933,f5936,f5944,f5958,f5968,f6036,f6068,f6070,f6136,f6138,f6142,f6144,f6255,f6437,f6587,f6663,f6749,f7116,f7830,f8224,f8267,f9254,f9276,f9277,f9294,f9410,f10672,f10731,f10733,f10761,f10845,f11062,f11197,f11283,f11499,f11830,f12577,f19493,f23101,f23184,f23186,f23201,f23374,f23414,f23419,f23490,f23598,f24902,f24907,f25519,f25896,f25997,f26109,f26192,f26349,f26528,f26685,f26834,f26860,f26980,f27622,f29129,f30537,f30544,f30551,f40724,f41833,f41838,f41843,f46873,f46892,f46895,f46899,f46906,f46918,f46919,f46920,f46922,f46927])).
% 31.56/4.35  fof(f46927,plain,(
% 31.56/4.35    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) != k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46922,plain,(
% 31.56/4.35    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1) | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46920,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))) | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46919,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))) | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46918,plain,(
% 31.56/4.35    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0) | ~v3_pre_topc(k1_xboole_0,sK0)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46906,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))) | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | sK1 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46899,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) != k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46895,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46892,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k1_xboole_0 != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) != k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) | k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))) | k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f46873,plain,(
% 31.56/4.35    ~spl4_1892 | ~spl4_2 | ~spl4_9 | ~spl4_1893),
% 31.56/4.35    inference(avatar_split_clause,[],[f46801,f41840,f216,f143,f41835])).
% 31.56/4.35  fof(f41835,plain,(
% 31.56/4.35    spl4_1892 <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1892])])).
% 31.56/4.35  fof(f143,plain,(
% 31.56/4.35    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 31.56/4.35  fof(f216,plain,(
% 31.56/4.35    spl4_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 31.56/4.35  fof(f41840,plain,(
% 31.56/4.35    spl4_1893 <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1893])])).
% 31.56/4.35  fof(f46801,plain,(
% 31.56/4.35    ~r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_9 | ~spl4_1893)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f41842,f3457])).
% 31.56/4.35  fof(f3457,plain,(
% 31.56/4.35    ( ! [X3] : (~r2_hidden(X3,k2_tops_1(sK0,sK1)) | ~r2_hidden(X3,sK1)) ) | (~spl4_2 | ~spl4_9)),
% 31.56/4.35    inference(superposition,[],[f1783,f144])).
% 31.56/4.35  fof(f144,plain,(
% 31.56/4.35    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 31.56/4.35    inference(avatar_component_clause,[],[f143])).
% 31.56/4.35  fof(f1783,plain,(
% 31.56/4.35    ( ! [X14,X13] : (~r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X13)) | ~r2_hidden(X14,X13)) ) | ~spl4_9),
% 31.56/4.35    inference(superposition,[],[f133,f298])).
% 31.56/4.35  fof(f298,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0)))) ) | ~spl4_9),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f218,f119])).
% 31.56/4.35  fof(f119,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.56/4.35    inference(definition_unfolding,[],[f95,f108])).
% 31.56/4.35  fof(f108,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 31.56/4.35    inference(definition_unfolding,[],[f83,f82])).
% 31.56/4.35  fof(f82,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f17])).
% 31.56/4.35  fof(f17,axiom,(
% 31.56/4.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 31.56/4.35  fof(f83,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f4])).
% 31.56/4.35  fof(f4,axiom,(
% 31.56/4.35    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 31.56/4.35  fof(f95,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f46])).
% 31.56/4.35  fof(f46,plain,(
% 31.56/4.35    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.56/4.35    inference(ennf_transformation,[],[f16])).
% 31.56/4.35  fof(f16,axiom,(
% 31.56/4.35    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 31.56/4.35  fof(f218,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 31.56/4.35    inference(avatar_component_clause,[],[f216])).
% 31.56/4.35  fof(f133,plain,(
% 31.56/4.35    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 31.56/4.35    inference(equality_resolution,[],[f124])).
% 31.56/4.35  fof(f124,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 31.56/4.35    inference(definition_unfolding,[],[f97,f108])).
% 31.56/4.35  fof(f97,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 31.56/4.35    inference(cnf_transformation,[],[f58])).
% 31.56/4.35  fof(f58,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 31.56/4.35  fof(f57,plain,(
% 31.56/4.35    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 31.56/4.35    introduced(choice_axiom,[])).
% 31.56/4.35  fof(f56,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(rectify,[],[f55])).
% 31.56/4.35  fof(f55,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(flattening,[],[f54])).
% 31.56/4.35  fof(f54,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(nnf_transformation,[],[f2])).
% 31.56/4.35  fof(f2,axiom,(
% 31.56/4.35    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 31.56/4.35  fof(f41842,plain,(
% 31.56/4.35    r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1) | ~spl4_1893),
% 31.56/4.35    inference(avatar_component_clause,[],[f41840])).
% 31.56/4.35  fof(f41843,plain,(
% 31.56/4.35    spl4_1893 | spl4_566 | ~spl4_3 | ~spl4_76 | ~spl4_358 | ~spl4_989),
% 31.56/4.35    inference(avatar_split_clause,[],[f41699,f19490,f4309,f845,f149,f11054,f41840])).
% 31.56/4.35  fof(f11054,plain,(
% 31.56/4.35    spl4_566 <=> k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_566])])).
% 31.56/4.35  fof(f149,plain,(
% 31.56/4.35    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 31.56/4.35  fof(f845,plain,(
% 31.56/4.35    spl4_76 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 31.56/4.35  fof(f4309,plain,(
% 31.56/4.35    spl4_358 <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_358])])).
% 31.56/4.35  fof(f19490,plain,(
% 31.56/4.35    spl4_989 <=> k1_xboole_0 = k7_subset_1(sK1,sK1,sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_989])])).
% 31.56/4.35  fof(f41699,plain,(
% 31.56/4.35    k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1) | (~spl4_3 | ~spl4_76 | ~spl4_358 | ~spl4_989)),
% 31.56/4.35    inference(resolution,[],[f41634,f4362])).
% 31.56/4.35  fof(f4362,plain,(
% 31.56/4.35    ( ! [X16] : (~r2_hidden(X16,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | r2_hidden(X16,sK1)) ) | ~spl4_358),
% 31.56/4.35    inference(superposition,[],[f137,f4311])).
% 31.56/4.35  fof(f4311,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl4_358),
% 31.56/4.35    inference(avatar_component_clause,[],[f4309])).
% 31.56/4.35  fof(f137,plain,(
% 31.56/4.35    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 31.56/4.35    inference(equality_resolution,[],[f131])).
% 31.56/4.35  fof(f131,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 31.56/4.35    inference(definition_unfolding,[],[f102,f82])).
% 31.56/4.35  fof(f102,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 31.56/4.35    inference(cnf_transformation,[],[f63])).
% 31.56/4.35  fof(f63,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).
% 31.56/4.35  fof(f62,plain,(
% 31.56/4.35    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 31.56/4.35    introduced(choice_axiom,[])).
% 31.56/4.35  fof(f61,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(rectify,[],[f60])).
% 31.56/4.35  fof(f60,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(flattening,[],[f59])).
% 31.56/4.35  fof(f59,plain,(
% 31.56/4.35    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 31.56/4.35    inference(nnf_transformation,[],[f1])).
% 31.56/4.35  fof(f1,axiom,(
% 31.56/4.35    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 31.56/4.35  fof(f41634,plain,(
% 31.56/4.35    ( ! [X3] : (r2_hidden(sK2(sK1,sK1,X3),X3) | k1_xboole_0 = X3) ) | (~spl4_3 | ~spl4_76 | ~spl4_989)),
% 31.56/4.35    inference(duplicate_literal_removal,[],[f41633])).
% 31.56/4.35  fof(f41633,plain,(
% 31.56/4.35    ( ! [X3] : (k1_xboole_0 = X3 | k1_xboole_0 = X3 | r2_hidden(sK2(sK1,sK1,X3),X3)) ) | (~spl4_3 | ~spl4_76 | ~spl4_989)),
% 31.56/4.35    inference(forward_demodulation,[],[f41632,f19492])).
% 31.56/4.35  fof(f19492,plain,(
% 31.56/4.35    k1_xboole_0 = k7_subset_1(sK1,sK1,sK1) | ~spl4_989),
% 31.56/4.35    inference(avatar_component_clause,[],[f19490])).
% 31.56/4.35  fof(f41632,plain,(
% 31.56/4.35    ( ! [X3] : (k7_subset_1(sK1,sK1,sK1) = X3 | k1_xboole_0 = X3 | r2_hidden(sK2(sK1,sK1,X3),X3)) ) | (~spl4_3 | ~spl4_76 | ~spl4_989)),
% 31.56/4.35    inference(forward_demodulation,[],[f41631,f19510])).
% 31.56/4.35  fof(f19510,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(sK1,sK1,X0)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(backward_demodulation,[],[f491,f19406])).
% 31.56/4.35  fof(f19406,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(backward_demodulation,[],[f181,f941])).
% 31.56/4.35  fof(f941,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0)) ) | ~spl4_76),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f847,f119])).
% 31.56/4.35  fof(f847,plain,(
% 31.56/4.35    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_76),
% 31.56/4.35    inference(avatar_component_clause,[],[f845])).
% 31.56/4.35  fof(f181,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl4_3),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f151,f119])).
% 31.56/4.35  fof(f151,plain,(
% 31.56/4.35    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 31.56/4.35    inference(avatar_component_clause,[],[f149])).
% 31.56/4.35  fof(f491,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f181,f81])).
% 31.56/4.35  fof(f81,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f13])).
% 31.56/4.35  fof(f13,axiom,(
% 31.56/4.35    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 31.56/4.35  fof(f41631,plain,(
% 31.56/4.35    ( ! [X3] : (k1_xboole_0 = X3 | r2_hidden(sK2(sK1,sK1,X3),X3) | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3) ) | (~spl4_3 | ~spl4_76 | ~spl4_989)),
% 31.56/4.35    inference(forward_demodulation,[],[f41607,f19492])).
% 31.56/4.35  fof(f41607,plain,(
% 31.56/4.35    ( ! [X3] : (r2_hidden(sK2(sK1,sK1,X3),X3) | k7_subset_1(sK1,sK1,sK1) = X3 | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(duplicate_literal_removal,[],[f41587])).
% 31.56/4.35  fof(f41587,plain,(
% 31.56/4.35    ( ! [X3] : (r2_hidden(sK2(sK1,sK1,X3),X3) | k7_subset_1(sK1,sK1,sK1) = X3 | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = X3 | r2_hidden(sK2(sK1,sK1,X3),X3)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(resolution,[],[f21048,f121])).
% 31.56/4.35  fof(f121,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f100,f108])).
% 31.56/4.35  fof(f100,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f58])).
% 31.56/4.35  fof(f21048,plain,(
% 31.56/4.35    ( ! [X0,X1] : (r2_hidden(sK2(sK1,X0,X1),X1) | r2_hidden(sK2(sK1,X0,X1),sK1) | k7_subset_1(sK1,sK1,X0) = X1) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(condensation,[],[f20993])).
% 31.56/4.35  fof(f20993,plain,(
% 31.56/4.35    ( ! [X8,X7,X9] : (r2_hidden(sK2(sK1,X7,X8),X8) | k7_subset_1(sK1,sK1,X7) = X8 | r2_hidden(sK2(sK1,X7,X8),X9) | r2_hidden(sK2(sK1,X7,X8),sK1)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(resolution,[],[f19599,f19514])).
% 31.56/4.35  fof(f19514,plain,(
% 31.56/4.35    ( ! [X15,X16] : (~r2_hidden(X16,k7_subset_1(sK1,sK1,X15)) | r2_hidden(X16,sK1)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(backward_demodulation,[],[f516,f19406])).
% 31.56/4.35  fof(f516,plain,(
% 31.56/4.35    ( ! [X15,X16] : (~r2_hidden(X16,k7_subset_1(u1_struct_0(sK0),sK1,X15)) | r2_hidden(X16,sK1)) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f134,f181])).
% 31.56/4.35  fof(f134,plain,(
% 31.56/4.35    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 31.56/4.35    inference(equality_resolution,[],[f125])).
% 31.56/4.35  fof(f125,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 31.56/4.35    inference(definition_unfolding,[],[f96,f108])).
% 31.56/4.35  fof(f96,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 31.56/4.35    inference(cnf_transformation,[],[f58])).
% 31.56/4.35  fof(f19599,plain,(
% 31.56/4.35    ( ! [X10,X11,X9] : (r2_hidden(sK2(sK1,X9,X10),k7_subset_1(sK1,sK1,X11)) | r2_hidden(sK2(sK1,X9,X10),X10) | k7_subset_1(sK1,sK1,X9) = X10 | r2_hidden(sK2(sK1,X9,X10),X11)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(forward_demodulation,[],[f19542,f19406])).
% 31.56/4.35  fof(f19542,plain,(
% 31.56/4.35    ( ! [X10,X11,X9] : (k7_subset_1(sK1,sK1,X9) = X10 | r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11)) | r2_hidden(sK2(sK1,X9,X10),X10) | r2_hidden(sK2(sK1,X9,X10),X11)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(backward_demodulation,[],[f1563,f19406])).
% 31.56/4.35  fof(f1563,plain,(
% 31.56/4.35    ( ! [X10,X11,X9] : (r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11)) | r2_hidden(sK2(sK1,X9,X10),X10) | k7_subset_1(u1_struct_0(sK0),sK1,X9) = X10 | r2_hidden(sK2(sK1,X9,X10),X11)) ) | ~spl4_3),
% 31.56/4.35    inference(forward_demodulation,[],[f1554,f181])).
% 31.56/4.35  fof(f1554,plain,(
% 31.56/4.35    ( ! [X10,X11,X9] : (r2_hidden(sK2(sK1,X9,X10),X11) | r2_hidden(sK2(sK1,X9,X10),k7_subset_1(u1_struct_0(sK0),sK1,X11)) | k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X9))) = X10 | r2_hidden(sK2(sK1,X9,X10),X10)) ) | ~spl4_3),
% 31.56/4.35    inference(resolution,[],[f514,f122])).
% 31.56/4.35  fof(f122,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f99,f108])).
% 31.56/4.35  fof(f99,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f58])).
% 31.56/4.35  fof(f514,plain,(
% 31.56/4.35    ( ! [X12,X11] : (~r2_hidden(X12,sK1) | r2_hidden(X12,X11) | r2_hidden(X12,k7_subset_1(u1_struct_0(sK0),sK1,X11))) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f132,f181])).
% 31.56/4.35  fof(f132,plain,(
% 31.56/4.35    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 31.56/4.35    inference(equality_resolution,[],[f123])).
% 31.56/4.35  fof(f123,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 31.56/4.35    inference(definition_unfolding,[],[f98,f108])).
% 31.56/4.35  fof(f98,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 31.56/4.35    inference(cnf_transformation,[],[f58])).
% 31.56/4.35  fof(f41838,plain,(
% 31.56/4.35    spl4_1892 | spl4_566 | ~spl4_3 | ~spl4_76 | ~spl4_358 | ~spl4_989),
% 31.56/4.35    inference(avatar_split_clause,[],[f41698,f19490,f4309,f845,f149,f11054,f41835])).
% 31.56/4.35  fof(f41698,plain,(
% 31.56/4.35    k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_76 | ~spl4_358 | ~spl4_989)),
% 31.56/4.35    inference(resolution,[],[f41634,f4361])).
% 31.56/4.35  fof(f4361,plain,(
% 31.56/4.35    ( ! [X15] : (~r2_hidden(X15,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | r2_hidden(X15,k2_tops_1(sK0,sK1))) ) | ~spl4_358),
% 31.56/4.35    inference(superposition,[],[f136,f4311])).
% 31.56/4.35  fof(f136,plain,(
% 31.56/4.35    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 31.56/4.35    inference(equality_resolution,[],[f130])).
% 31.56/4.35  fof(f130,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 31.56/4.35    inference(definition_unfolding,[],[f103,f82])).
% 31.56/4.35  fof(f103,plain,(
% 31.56/4.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 31.56/4.35    inference(cnf_transformation,[],[f63])).
% 31.56/4.35  fof(f41833,plain,(
% 31.56/4.35    ~spl4_1891 | spl4_566 | ~spl4_3 | ~spl4_76 | ~spl4_368 | ~spl4_989),
% 31.56/4.35    inference(avatar_split_clause,[],[f41697,f19490,f4435,f845,f149,f11054,f41830])).
% 31.56/4.35  fof(f41830,plain,(
% 31.56/4.35    spl4_1891 <=> r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1891])])).
% 31.56/4.35  fof(f4435,plain,(
% 31.56/4.35    spl4_368 <=> k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_368])])).
% 31.56/4.35  fof(f41697,plain,(
% 31.56/4.35    k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK2(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_76 | ~spl4_368 | ~spl4_989)),
% 31.56/4.35    inference(resolution,[],[f41634,f4441])).
% 31.56/4.35  fof(f4441,plain,(
% 31.56/4.35    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~r2_hidden(X0,k1_tops_1(sK0,sK1))) ) | (~spl4_3 | ~spl4_368)),
% 31.56/4.35    inference(superposition,[],[f515,f4437])).
% 31.56/4.35  fof(f4437,plain,(
% 31.56/4.35    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl4_368),
% 31.56/4.35    inference(avatar_component_clause,[],[f4435])).
% 31.56/4.35  fof(f515,plain,(
% 31.56/4.35    ( ! [X14,X13] : (~r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),sK1,X13)) | ~r2_hidden(X14,X13)) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f133,f181])).
% 31.56/4.35  fof(f40724,plain,(
% 31.56/4.35    sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | k2_pre_topc(sK0,sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) | k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) != k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f30551,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | sK1 != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~v3_pre_topc(sK1,sK0)),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f30544,plain,(
% 31.56/4.35    spl4_1422 | ~spl4_18 | ~spl4_428 | ~spl4_1089 | ~spl4_1377),
% 31.56/4.35    inference(avatar_split_clause,[],[f30539,f29126,f23150,f5203,f285,f30541])).
% 31.56/4.35  fof(f30541,plain,(
% 31.56/4.35    spl4_1422 <=> sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1422])])).
% 31.56/4.35  fof(f285,plain,(
% 31.56/4.35    spl4_18 <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 31.56/4.35  fof(f5203,plain,(
% 31.56/4.35    spl4_428 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_428])])).
% 31.56/4.35  fof(f23150,plain,(
% 31.56/4.35    spl4_1089 <=> u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1089])])).
% 31.56/4.35  fof(f29126,plain,(
% 31.56/4.35    spl4_1377 <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1377])])).
% 31.56/4.35  fof(f30539,plain,(
% 31.56/4.35    sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_18 | ~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(forward_demodulation,[],[f30538,f287])).
% 31.56/4.35  fof(f287,plain,(
% 31.56/4.35    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl4_18),
% 31.56/4.35    inference(avatar_component_clause,[],[f285])).
% 31.56/4.35  fof(f30538,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(forward_demodulation,[],[f30526,f81])).
% 31.56/4.35  fof(f30526,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(superposition,[],[f27039,f29128])).
% 31.56/4.35  fof(f29128,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | ~spl4_1377),
% 31.56/4.35    inference(avatar_component_clause,[],[f29126])).
% 31.56/4.35  fof(f27039,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(u1_struct_0(sK0),X1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1))) ) | (~spl4_428 | ~spl4_1089)),
% 31.56/4.35    inference(backward_demodulation,[],[f23456,f23151])).
% 31.56/4.35  fof(f23151,plain,(
% 31.56/4.35    u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) | ~spl4_1089),
% 31.56/4.35    inference(avatar_component_clause,[],[f23150])).
% 31.56/4.35  fof(f23456,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))) ) | ~spl4_428),
% 31.56/4.35    inference(forward_demodulation,[],[f23430,f11996])).
% 31.56/4.35  fof(f11996,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0)))) ) | ~spl4_428),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5205,f119])).
% 31.56/4.35  fof(f5205,plain,(
% 31.56/4.35    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_428),
% 31.56/4.35    inference(avatar_component_clause,[],[f5203])).
% 31.56/4.35  fof(f23430,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))))) ) | ~spl4_428),
% 31.56/4.35    inference(superposition,[],[f11996,f113])).
% 31.56/4.35  fof(f113,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 31.56/4.35    inference(definition_unfolding,[],[f84,f82,f108,f108])).
% 31.56/4.35  fof(f84,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f11])).
% 31.56/4.35  fof(f11,axiom,(
% 31.56/4.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 31.56/4.35  fof(f30537,plain,(
% 31.56/4.35    spl4_1421 | ~spl4_18 | ~spl4_75 | ~spl4_428 | ~spl4_1089 | ~spl4_1377),
% 31.56/4.35    inference(avatar_split_clause,[],[f30532,f29126,f23150,f5203,f834,f285,f30534])).
% 31.56/4.35  fof(f30534,plain,(
% 31.56/4.35    spl4_1421 <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1421])])).
% 31.56/4.35  fof(f834,plain,(
% 31.56/4.35    spl4_75 <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 31.56/4.35  fof(f30532,plain,(
% 31.56/4.35    sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_18 | ~spl4_75 | ~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(forward_demodulation,[],[f30531,f287])).
% 31.56/4.35  fof(f30531,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_75 | ~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(forward_demodulation,[],[f30530,f81])).
% 31.56/4.35  fof(f30530,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_75 | ~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(forward_demodulation,[],[f30524,f836])).
% 31.56/4.35  fof(f836,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | ~spl4_75),
% 31.56/4.35    inference(avatar_component_clause,[],[f834])).
% 31.56/4.35  fof(f30524,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_428 | ~spl4_1089 | ~spl4_1377)),
% 31.56/4.35    inference(superposition,[],[f27035,f29128])).
% 31.56/4.35  fof(f27035,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(u1_struct_0(sK0),X1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1))))) ) | (~spl4_428 | ~spl4_1089)),
% 31.56/4.35    inference(backward_demodulation,[],[f23438,f23151])).
% 31.56/4.35  fof(f23438,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1)) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X1))))) ) | ~spl4_428),
% 31.56/4.35    inference(superposition,[],[f113,f11996])).
% 31.56/4.35  fof(f29129,plain,(
% 31.56/4.35    spl4_1377 | ~spl4_18 | ~spl4_428 | ~spl4_1089),
% 31.56/4.35    inference(avatar_split_clause,[],[f29106,f23150,f5203,f285,f29126])).
% 31.56/4.35  fof(f29106,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | (~spl4_18 | ~spl4_428 | ~spl4_1089)),
% 31.56/4.35    inference(superposition,[],[f27033,f287])).
% 31.56/4.35  fof(f27033,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0)))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)) ) | (~spl4_428 | ~spl4_1089)),
% 31.56/4.35    inference(backward_demodulation,[],[f23420,f23151])).
% 31.56/4.35  fof(f23420,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_setfam_1(k2_tarski(X0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) ) | ~spl4_428),
% 31.56/4.35    inference(superposition,[],[f11996,f81])).
% 31.56/4.35  fof(f27622,plain,(
% 31.56/4.35    spl4_1334 | ~spl4_123 | ~spl4_601),
% 31.56/4.35    inference(avatar_split_clause,[],[f27558,f12069,f1323,f27608])).
% 31.56/4.35  fof(f27608,plain,(
% 31.56/4.35    spl4_1334 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1334])])).
% 31.56/4.35  fof(f1323,plain,(
% 31.56/4.35    spl4_123 <=> k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).
% 31.56/4.35  fof(f12069,plain,(
% 31.56/4.35    spl4_601 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_601])])).
% 31.56/4.35  fof(f27558,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) | (~spl4_123 | ~spl4_601)),
% 31.56/4.35    inference(superposition,[],[f1325,f12079])).
% 31.56/4.35  fof(f12079,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)) ) | ~spl4_601),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f12071,f119])).
% 31.56/4.35  fof(f12071,plain,(
% 31.56/4.35    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_601),
% 31.56/4.35    inference(avatar_component_clause,[],[f12069])).
% 31.56/4.35  fof(f1325,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))) | ~spl4_123),
% 31.56/4.35    inference(avatar_component_clause,[],[f1323])).
% 31.56/4.35  fof(f26980,plain,(
% 31.56/4.35    spl4_432 | ~spl4_4 | ~spl4_425 | ~spl4_428),
% 31.56/4.35    inference(avatar_split_clause,[],[f26977,f5203,f5188,f154,f5223])).
% 31.56/4.35  fof(f5223,plain,(
% 31.56/4.35    spl4_432 <=> k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_432])])).
% 31.56/4.35  fof(f154,plain,(
% 31.56/4.35    spl4_4 <=> l1_pre_topc(sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 31.56/4.35  fof(f5188,plain,(
% 31.56/4.35    spl4_425 <=> v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_425])])).
% 31.56/4.35  fof(f26977,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | (~spl4_4 | ~spl4_425 | ~spl4_428)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f156,f5205,f5189,f75])).
% 31.56/4.35  fof(f75,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f37])).
% 31.56/4.35  fof(f37,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(flattening,[],[f36])).
% 31.56/4.35  fof(f36,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(ennf_transformation,[],[f20])).
% 31.56/4.35  fof(f20,axiom,(
% 31.56/4.35    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 31.56/4.35  fof(f5189,plain,(
% 31.56/4.35    v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0) | ~spl4_425),
% 31.56/4.35    inference(avatar_component_clause,[],[f5188])).
% 31.56/4.35  fof(f156,plain,(
% 31.56/4.35    l1_pre_topc(sK0) | ~spl4_4),
% 31.56/4.35    inference(avatar_component_clause,[],[f154])).
% 31.56/4.35  fof(f26860,plain,(
% 31.56/4.35    spl4_595 | ~spl4_3 | ~spl4_44 | ~spl4_150 | ~spl4_167 | ~spl4_407 | ~spl4_412),
% 31.56/4.35    inference(avatar_split_clause,[],[f26859,f5116,f5089,f1936,f1659,f529,f149,f11961])).
% 31.56/4.35  fof(f11961,plain,(
% 31.56/4.35    spl4_595 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_595])])).
% 31.56/4.35  fof(f529,plain,(
% 31.56/4.35    spl4_44 <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 31.56/4.35  fof(f1659,plain,(
% 31.56/4.35    spl4_150 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).
% 31.56/4.35  fof(f1936,plain,(
% 31.56/4.35    spl4_167 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).
% 31.56/4.35  fof(f5089,plain,(
% 31.56/4.35    spl4_407 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_407])])).
% 31.56/4.35  fof(f5116,plain,(
% 31.56/4.35    spl4_412 <=> k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_412])])).
% 31.56/4.35  fof(f26859,plain,(
% 31.56/4.35    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl4_3 | ~spl4_44 | ~spl4_150 | ~spl4_167 | ~spl4_407 | ~spl4_412)),
% 31.56/4.35    inference(forward_demodulation,[],[f5118,f11828])).
% 31.56/4.35  fof(f11828,plain,(
% 31.56/4.35    ( ! [X0] : (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_44 | ~spl4_150 | ~spl4_167 | ~spl4_407)),
% 31.56/4.35    inference(forward_demodulation,[],[f11827,f1938])).
% 31.56/4.35  fof(f1938,plain,(
% 31.56/4.35    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_167),
% 31.56/4.35    inference(avatar_component_clause,[],[f1936])).
% 31.56/4.35  fof(f11827,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_44 | ~spl4_150 | ~spl4_407)),
% 31.56/4.35    inference(forward_demodulation,[],[f11797,f1894])).
% 31.56/4.35  fof(f1894,plain,(
% 31.56/4.35    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ) | (~spl4_3 | ~spl4_44 | ~spl4_150)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f1862,f1862,f128])).
% 31.56/4.35  fof(f128,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f105,f82])).
% 31.56/4.35  fof(f105,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f63])).
% 31.56/4.35  fof(f1862,plain,(
% 31.56/4.35    ( ! [X15] : (~r2_hidden(X15,k1_xboole_0)) ) | (~spl4_3 | ~spl4_44 | ~spl4_150)),
% 31.56/4.35    inference(subsumption_resolution,[],[f1845,f1262])).
% 31.56/4.35  fof(f1262,plain,(
% 31.56/4.35    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl4_3 | ~spl4_44)),
% 31.56/4.35    inference(superposition,[],[f515,f531])).
% 31.56/4.35  fof(f531,plain,(
% 31.56/4.35    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl4_44),
% 31.56/4.35    inference(avatar_component_clause,[],[f529])).
% 31.56/4.35  fof(f1845,plain,(
% 31.56/4.35    ( ! [X15] : (~r2_hidden(X15,k1_xboole_0) | r2_hidden(X15,sK1)) ) | ~spl4_150),
% 31.56/4.35    inference(superposition,[],[f136,f1661])).
% 31.56/4.35  fof(f1661,plain,(
% 31.56/4.35    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) | ~spl4_150),
% 31.56/4.35    inference(avatar_component_clause,[],[f1659])).
% 31.56/4.35  fof(f11797,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X0)) ) | ~spl4_407),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5091,f119])).
% 31.56/4.35  fof(f5091,plain,(
% 31.56/4.35    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_407),
% 31.56/4.35    inference(avatar_component_clause,[],[f5089])).
% 31.56/4.35  fof(f5118,plain,(
% 31.56/4.35    k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) | ~spl4_412),
% 31.56/4.35    inference(avatar_component_clause,[],[f5116])).
% 31.56/4.35  fof(f26834,plain,(
% 31.56/4.35    spl4_405 | ~spl4_410 | ~spl4_595),
% 31.56/4.35    inference(avatar_split_clause,[],[f12172,f11961,f5106,f5079])).
% 31.56/4.35  fof(f5079,plain,(
% 31.56/4.35    spl4_405 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_405])])).
% 31.56/4.35  fof(f5106,plain,(
% 31.56/4.35    spl4_410 <=> v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_410])])).
% 31.56/4.35  fof(f12172,plain,(
% 31.56/4.35    v3_pre_topc(k1_xboole_0,sK0) | (~spl4_410 | ~spl4_595)),
% 31.56/4.35    inference(backward_demodulation,[],[f5108,f11963])).
% 31.56/4.35  fof(f11963,plain,(
% 31.56/4.35    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl4_595),
% 31.56/4.35    inference(avatar_component_clause,[],[f11961])).
% 31.56/4.35  fof(f5108,plain,(
% 31.56/4.35    v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0) | ~spl4_410),
% 31.56/4.35    inference(avatar_component_clause,[],[f5106])).
% 31.56/4.35  fof(f26685,plain,(
% 31.56/4.35    spl4_412 | ~spl4_3 | ~spl4_4 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150),
% 31.56/4.35    inference(avatar_split_clause,[],[f26648,f1659,f1579,f845,f529,f154,f149,f5116])).
% 31.56/4.35  fof(f1579,plain,(
% 31.56/4.35    spl4_144 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).
% 31.56/4.35  fof(f26648,plain,(
% 31.56/4.35    k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_4 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f156,f26529,f72])).
% 31.56/4.35  fof(f72,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f33])).
% 31.56/4.35  fof(f33,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(ennf_transformation,[],[f26])).
% 31.56/4.35  fof(f26,axiom,(
% 31.56/4.35    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 31.56/4.35  fof(f26529,plain,(
% 31.56/4.35    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f25874,f91])).
% 31.56/4.35  fof(f91,plain,(
% 31.56/4.35    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f53])).
% 31.56/4.35  fof(f53,plain,(
% 31.56/4.35    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.56/4.35    inference(nnf_transformation,[],[f18])).
% 31.56/4.35  fof(f18,axiom,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 31.56/4.35  fof(f25874,plain,(
% 31.56/4.35    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(superposition,[],[f112,f22985])).
% 31.56/4.35  fof(f22985,plain,(
% 31.56/4.35    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X3,k1_xboole_0))))) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(superposition,[],[f113,f22914])).
% 31.56/4.35  fof(f22914,plain,(
% 31.56/4.35    ( ! [X4] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4)))) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(subsumption_resolution,[],[f22910,f1862])).
% 31.56/4.35  fof(f22910,plain,(
% 31.56/4.35    ( ! [X4] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4))) | r2_hidden(sK3(X4,k7_subset_1(sK1,sK1,X4),k1_xboole_0),k1_xboole_0)) ) | (~spl4_3 | ~spl4_76 | ~spl4_144)),
% 31.56/4.35    inference(duplicate_literal_removal,[],[f22868])).
% 31.56/4.35  fof(f22868,plain,(
% 31.56/4.35    ( ! [X4] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4))) | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k7_subset_1(sK1,sK1,X4))) | r2_hidden(sK3(X4,k7_subset_1(sK1,sK1,X4),k1_xboole_0),k1_xboole_0)) ) | (~spl4_3 | ~spl4_76 | ~spl4_144)),
% 31.56/4.35    inference(resolution,[],[f16499,f19575])).
% 31.56/4.35  fof(f19575,plain,(
% 31.56/4.35    ( ! [X26,X24,X25] : (~r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25) | k1_setfam_1(k2_tarski(X24,k7_subset_1(sK1,sK1,X25))) = X26 | r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X26)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(forward_demodulation,[],[f19574,f19406])).
% 31.56/4.35  fof(f19574,plain,(
% 31.56/4.35    ( ! [X26,X24,X25] : (k1_setfam_1(k2_tarski(X24,k7_subset_1(sK1,sK1,X25))) = X26 | ~r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25) | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(forward_demodulation,[],[f19523,f19406])).
% 31.56/4.35  fof(f19523,plain,(
% 31.56/4.35    ( ! [X26,X24,X25] : (~r2_hidden(sK3(X24,k7_subset_1(sK1,sK1,X25),X26),X25) | k1_setfam_1(k2_tarski(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25))) = X26 | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26)) ) | (~spl4_3 | ~spl4_76)),
% 31.56/4.35    inference(backward_demodulation,[],[f1257,f19406])).
% 31.56/4.35  fof(f1257,plain,(
% 31.56/4.35    ( ! [X26,X24,X25] : (~r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X25) | k1_setfam_1(k2_tarski(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25))) = X26 | r2_hidden(sK3(X24,k7_subset_1(u1_struct_0(sK0),sK1,X25),X26),X26)) ) | ~spl4_3),
% 31.56/4.35    inference(resolution,[],[f515,f127])).
% 31.56/4.35  fof(f127,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f106,f82])).
% 31.56/4.35  fof(f106,plain,(
% 31.56/4.35    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f63])).
% 31.56/4.35  fof(f16499,plain,(
% 31.56/4.35    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3))) ) | (~spl4_3 | ~spl4_144)),
% 31.56/4.35    inference(forward_demodulation,[],[f16498,f1581])).
% 31.56/4.35  fof(f1581,plain,(
% 31.56/4.35    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) | ~spl4_144),
% 31.56/4.35    inference(avatar_component_clause,[],[f1579])).
% 31.56/4.35  fof(f16498,plain,(
% 31.56/4.35    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k1_xboole_0),X2) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3))) ) | (~spl4_3 | ~spl4_144)),
% 31.56/4.35    inference(forward_demodulation,[],[f16493,f1581])).
% 31.56/4.35  fof(f16493,plain,(
% 31.56/4.35    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3))) ) | ~spl4_3),
% 31.56/4.35    inference(duplicate_literal_removal,[],[f16409])).
% 31.56/4.35  fof(f16409,plain,(
% 31.56/4.35    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3)) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(X2,X3)) | r2_hidden(sK3(X2,X3,k7_subset_1(u1_struct_0(sK0),sK1,sK1)),X2)) ) | ~spl4_3),
% 31.56/4.35    inference(resolution,[],[f1274,f1258])).
% 31.56/4.35  fof(f1258,plain,(
% 31.56/4.35    ( ! [X28,X29,X27] : (~r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X29) | k7_subset_1(u1_struct_0(sK0),sK1,X29) = k1_setfam_1(k2_tarski(X27,X28)) | r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X27)) ) | ~spl4_3),
% 31.56/4.35    inference(resolution,[],[f515,f128])).
% 31.56/4.35  fof(f1274,plain,(
% 31.56/4.35    ( ! [X28,X29,X27] : (r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),sK1) | r2_hidden(sK3(X27,X28,k7_subset_1(u1_struct_0(sK0),sK1,X29)),X27) | k7_subset_1(u1_struct_0(sK0),sK1,X29) = k1_setfam_1(k2_tarski(X27,X28))) ) | ~spl4_3),
% 31.56/4.35    inference(resolution,[],[f516,f128])).
% 31.56/4.35  fof(f112,plain,(
% 31.56/4.35    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f80,f108])).
% 31.56/4.35  fof(f80,plain,(
% 31.56/4.35    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f9])).
% 31.56/4.35  fof(f9,axiom,(
% 31.56/4.35    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 31.56/4.35  fof(f26528,plain,(
% 31.56/4.35    spl4_588 | ~spl4_407),
% 31.56/4.35    inference(avatar_split_clause,[],[f26527,f5089,f11822])).
% 31.56/4.35  fof(f11822,plain,(
% 31.56/4.35    spl4_588 <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_588])])).
% 31.56/4.35  fof(f26527,plain,(
% 31.56/4.35    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl4_407),
% 31.56/4.35    inference(forward_demodulation,[],[f26500,f110])).
% 31.56/4.35  fof(f110,plain,(
% 31.56/4.35    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 31.56/4.35    inference(definition_unfolding,[],[f70,f108])).
% 31.56/4.35  fof(f70,plain,(
% 31.56/4.35    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.56/4.35    inference(cnf_transformation,[],[f10])).
% 31.56/4.35  fof(f10,axiom,(
% 31.56/4.35    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 31.56/4.35  fof(f26500,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0))) | ~spl4_407),
% 31.56/4.35    inference(resolution,[],[f5091,f115])).
% 31.56/4.35  fof(f115,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.56/4.35    inference(definition_unfolding,[],[f87,f108])).
% 31.56/4.35  fof(f87,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f41])).
% 31.56/4.35  fof(f41,plain,(
% 31.56/4.35    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.56/4.35    inference(ennf_transformation,[],[f14])).
% 31.56/4.35  fof(f14,axiom,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 31.56/4.35  fof(f26349,plain,(
% 31.56/4.35    spl4_407 | ~spl4_408),
% 31.56/4.35    inference(avatar_split_clause,[],[f11866,f5096,f5089])).
% 31.56/4.35  fof(f5096,plain,(
% 31.56/4.35    spl4_408 <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_408])])).
% 31.56/4.35  fof(f11866,plain,(
% 31.56/4.35    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_408),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5098,f91])).
% 31.56/4.35  fof(f5098,plain,(
% 31.56/4.35    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl4_408),
% 31.56/4.35    inference(avatar_component_clause,[],[f5096])).
% 31.56/4.35  fof(f26192,plain,(
% 31.56/4.35    spl4_630 | ~spl4_491),
% 31.56/4.35    inference(avatar_split_clause,[],[f12509,f5536,f12527])).
% 31.56/4.35  fof(f12527,plain,(
% 31.56/4.35    spl4_630 <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_630])])).
% 31.56/4.35  fof(f5536,plain,(
% 31.56/4.35    spl4_491 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_491])])).
% 31.56/4.35  fof(f12509,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | ~spl4_491),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5538,f115])).
% 31.56/4.35  fof(f5538,plain,(
% 31.56/4.35    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_491),
% 31.56/4.35    inference(avatar_component_clause,[],[f5536])).
% 31.56/4.35  fof(f26109,plain,(
% 31.56/4.35    ~spl4_407 | spl4_601 | ~spl4_588),
% 31.56/4.35    inference(avatar_split_clause,[],[f11981,f11822,f12069,f5089])).
% 31.56/4.35  fof(f11981,plain,(
% 31.56/4.35    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_588),
% 31.56/4.35    inference(superposition,[],[f86,f11824])).
% 31.56/4.35  fof(f11824,plain,(
% 31.56/4.35    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl4_588),
% 31.56/4.35    inference(avatar_component_clause,[],[f11822])).
% 31.56/4.35  fof(f86,plain,(
% 31.56/4.35    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f40])).
% 31.56/4.35  fof(f40,plain,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.56/4.35    inference(ennf_transformation,[],[f15])).
% 31.56/4.35  fof(f15,axiom,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 31.56/4.35  fof(f25997,plain,(
% 31.56/4.35    spl4_643 | ~spl4_641),
% 31.56/4.35    inference(avatar_split_clause,[],[f12710,f12692,f12727])).
% 31.56/4.35  fof(f12727,plain,(
% 31.56/4.35    spl4_643 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_643])])).
% 31.56/4.35  fof(f12692,plain,(
% 31.56/4.35    spl4_641 <=> k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_641])])).
% 31.56/4.35  fof(f12710,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | ~spl4_641),
% 31.56/4.35    inference(superposition,[],[f113,f12694])).
% 31.56/4.35  fof(f12694,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | ~spl4_641),
% 31.56/4.35    inference(avatar_component_clause,[],[f12692])).
% 31.56/4.35  fof(f25896,plain,(
% 31.56/4.35    spl4_1144 | ~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | ~spl4_596),
% 31.56/4.35    inference(avatar_split_clause,[],[f25845,f12016,f1659,f1579,f845,f529,f149,f23951])).
% 31.56/4.35  fof(f23951,plain,(
% 31.56/4.35    spl4_1144 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1144])])).
% 31.56/4.35  fof(f12016,plain,(
% 31.56/4.35    spl4_596 <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_596])])).
% 31.56/4.35  fof(f25845,plain,(
% 31.56/4.35    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | ~spl4_596)),
% 31.56/4.35    inference(backward_demodulation,[],[f12018,f22985])).
% 31.56/4.35  fof(f12018,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | ~spl4_596),
% 31.56/4.35    inference(avatar_component_clause,[],[f12016])).
% 31.56/4.35  fof(f25519,plain,(
% 31.56/4.35    spl4_1235 | ~spl4_1188),
% 31.56/4.35    inference(avatar_split_clause,[],[f25518,f24899,f25509])).
% 31.56/4.35  fof(f25509,plain,(
% 31.56/4.35    spl4_1235 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1235])])).
% 31.56/4.35  fof(f24899,plain,(
% 31.56/4.35    spl4_1188 <=> r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1188])])).
% 31.56/4.35  fof(f25518,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | ~spl4_1188),
% 31.56/4.35    inference(forward_demodulation,[],[f25502,f81])).
% 31.56/4.35  fof(f25502,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0))) | ~spl4_1188),
% 31.56/4.35    inference(resolution,[],[f24901,f114])).
% 31.56/4.35  fof(f114,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 31.56/4.35    inference(definition_unfolding,[],[f85,f82])).
% 31.56/4.35  fof(f85,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f39])).
% 31.56/4.35  fof(f39,plain,(
% 31.56/4.35    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.56/4.35    inference(ennf_transformation,[],[f7])).
% 31.56/4.35  fof(f7,axiom,(
% 31.56/4.35    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 31.56/4.35  fof(f24901,plain,(
% 31.56/4.35    r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0)) | ~spl4_1188),
% 31.56/4.35    inference(avatar_component_clause,[],[f24899])).
% 31.56/4.35  fof(f24907,plain,(
% 31.56/4.35    spl4_1189 | ~spl4_1103),
% 31.56/4.35    inference(avatar_split_clause,[],[f24882,f23416,f24904])).
% 31.56/4.35  fof(f24904,plain,(
% 31.56/4.35    spl4_1189 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1189])])).
% 31.56/4.35  fof(f23416,plain,(
% 31.56/4.35    spl4_1103 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1103])])).
% 31.56/4.35  fof(f24882,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))))) | ~spl4_1103),
% 31.56/4.35    inference(superposition,[],[f113,f23418])).
% 31.56/4.35  fof(f23418,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | ~spl4_1103),
% 31.56/4.35    inference(avatar_component_clause,[],[f23416])).
% 31.56/4.35  fof(f24902,plain,(
% 31.56/4.35    spl4_1188 | ~spl4_1103),
% 31.56/4.35    inference(avatar_split_clause,[],[f24881,f23416,f24899])).
% 31.56/4.35  fof(f24881,plain,(
% 31.56/4.35    r1_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))),u1_struct_0(sK0)) | ~spl4_1103),
% 31.56/4.35    inference(superposition,[],[f112,f23418])).
% 31.56/4.35  fof(f23598,plain,(
% 31.56/4.35    spl4_1114 | ~spl4_451),
% 31.56/4.35    inference(avatar_split_clause,[],[f23597,f5322,f23593])).
% 31.56/4.35  fof(f23593,plain,(
% 31.56/4.35    spl4_1114 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1114])])).
% 31.56/4.35  fof(f5322,plain,(
% 31.56/4.35    spl4_451 <=> r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_451])])).
% 31.56/4.35  fof(f23597,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | ~spl4_451),
% 31.56/4.35    inference(forward_demodulation,[],[f23589,f81])).
% 31.56/4.35  fof(f23589,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))) | ~spl4_451),
% 31.56/4.35    inference(resolution,[],[f5324,f114])).
% 31.56/4.35  fof(f5324,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) | ~spl4_451),
% 31.56/4.35    inference(avatar_component_clause,[],[f5322])).
% 31.56/4.35  fof(f23490,plain,(
% 31.56/4.35    ~spl4_1090 | ~spl4_3 | ~spl4_4 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | spl4_425),
% 31.56/4.35    inference(avatar_split_clause,[],[f23464,f5188,f1659,f1579,f845,f529,f154,f149,f23188])).
% 31.56/4.35  fof(f23188,plain,(
% 31.56/4.35    spl4_1090 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1090])])).
% 31.56/4.35  fof(f23464,plain,(
% 31.56/4.35    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | spl4_425)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f156,f5190,f23087,f78])).
% 31.56/4.35  fof(f78,plain,(
% 31.56/4.35    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f52])).
% 31.56/4.35  fof(f52,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(nnf_transformation,[],[f38])).
% 31.56/4.35  fof(f38,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(ennf_transformation,[],[f24])).
% 31.56/4.35  fof(f24,axiom,(
% 31.56/4.35    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 31.56/4.35  fof(f23087,plain,(
% 31.56/4.35    ( ! [X0] : (m1_subset_1(k5_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X0))) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f22984,f91])).
% 31.56/4.35  fof(f22984,plain,(
% 31.56/4.35    ( ! [X2] : (r1_tarski(k5_xboole_0(X2,k1_xboole_0),X2)) ) | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150)),
% 31.56/4.35    inference(superposition,[],[f112,f22914])).
% 31.56/4.35  fof(f5190,plain,(
% 31.56/4.35    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),sK0) | spl4_425),
% 31.56/4.35    inference(avatar_component_clause,[],[f5188])).
% 31.56/4.35  fof(f23419,plain,(
% 31.56/4.35    spl4_1103 | ~spl4_596),
% 31.56/4.35    inference(avatar_split_clause,[],[f23400,f12016,f23416])).
% 31.56/4.35  fof(f23400,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0))))) | ~spl4_596),
% 31.56/4.35    inference(superposition,[],[f113,f12018])).
% 31.56/4.35  fof(f23414,plain,(
% 31.56/4.35    spl4_1053 | ~spl4_596),
% 31.56/4.35    inference(avatar_split_clause,[],[f23399,f12016,f22580])).
% 31.56/4.35  fof(f22580,plain,(
% 31.56/4.35    spl4_1053 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_1053])])).
% 31.56/4.35  fof(f23399,plain,(
% 31.56/4.35    r1_tarski(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) | ~spl4_596),
% 31.56/4.35    inference(superposition,[],[f112,f12018])).
% 31.56/4.35  fof(f23374,plain,(
% 31.56/4.35    spl4_451 | ~spl4_430),
% 31.56/4.35    inference(avatar_split_clause,[],[f23330,f5213,f5322])).
% 31.56/4.35  fof(f5213,plain,(
% 31.56/4.35    spl4_430 <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_430])])).
% 31.56/4.35  fof(f23330,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(sK0)) | ~spl4_430),
% 31.56/4.35    inference(resolution,[],[f5215,f90])).
% 31.56/4.35  fof(f90,plain,(
% 31.56/4.35    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.56/4.35    inference(cnf_transformation,[],[f53])).
% 31.56/4.35  fof(f5215,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_430),
% 31.56/4.35    inference(avatar_component_clause,[],[f5213])).
% 31.56/4.35  fof(f23201,plain,(
% 31.56/4.35    spl4_596 | ~spl4_428),
% 31.56/4.35    inference(avatar_split_clause,[],[f23182,f5203,f12016])).
% 31.56/4.35  fof(f23182,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)))) | ~spl4_428),
% 31.56/4.35    inference(resolution,[],[f5205,f115])).
% 31.56/4.35  fof(f23186,plain,(
% 31.56/4.35    spl4_430 | ~spl4_4 | ~spl4_428),
% 31.56/4.35    inference(avatar_split_clause,[],[f23165,f5203,f154,f5213])).
% 31.56/4.35  fof(f23165,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_428)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f156,f5205,f89])).
% 31.56/4.35  fof(f89,plain,(
% 31.56/4.35    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f45])).
% 31.56/4.35  fof(f45,plain,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(flattening,[],[f44])).
% 31.56/4.35  fof(f44,plain,(
% 31.56/4.35    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.56/4.35    inference(ennf_transformation,[],[f19])).
% 31.56/4.35  fof(f19,axiom,(
% 31.56/4.35    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 31.56/4.35  fof(f23184,plain,(
% 31.56/4.35    spl4_544 | ~spl4_428),
% 31.56/4.35    inference(avatar_split_clause,[],[f23169,f5203,f9206])).
% 31.56/4.35  fof(f9206,plain,(
% 31.56/4.35    spl4_544 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_544])])).
% 31.56/4.35  fof(f23169,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_428),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5205,f86])).
% 31.56/4.35  fof(f23101,plain,(
% 31.56/4.35    ~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | spl4_428),
% 31.56/4.35    inference(avatar_contradiction_clause,[],[f23088])).
% 31.56/4.35  fof(f23088,plain,(
% 31.56/4.35    $false | (~spl4_3 | ~spl4_44 | ~spl4_76 | ~spl4_144 | ~spl4_150 | spl4_428)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f5204,f22984,f91])).
% 31.56/4.35  fof(f5204,plain,(
% 31.56/4.35    ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_428),
% 31.56/4.35    inference(avatar_component_clause,[],[f5203])).
% 31.56/4.35  fof(f19493,plain,(
% 31.56/4.35    spl4_989 | ~spl4_76 | ~spl4_148),
% 31.56/4.35    inference(avatar_split_clause,[],[f19488,f1643,f845,f19490])).
% 31.56/4.35  fof(f1643,plain,(
% 31.56/4.35    spl4_148 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).
% 31.56/4.35  fof(f19488,plain,(
% 31.56/4.35    k1_xboole_0 = k7_subset_1(sK1,sK1,sK1) | (~spl4_76 | ~spl4_148)),
% 31.56/4.35    inference(forward_demodulation,[],[f19419,f1645])).
% 31.56/4.35  fof(f1645,plain,(
% 31.56/4.35    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl4_148),
% 31.56/4.35    inference(avatar_component_clause,[],[f1643])).
% 31.56/4.35  fof(f19419,plain,(
% 31.56/4.35    k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,sK1) | ~spl4_76),
% 31.56/4.35    inference(superposition,[],[f941,f111])).
% 31.56/4.35  fof(f111,plain,(
% 31.56/4.35    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 31.56/4.35    inference(definition_unfolding,[],[f79,f82])).
% 31.56/4.35  fof(f79,plain,(
% 31.56/4.35    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.56/4.35    inference(cnf_transformation,[],[f29])).
% 31.56/4.35  fof(f29,plain,(
% 31.56/4.35    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.56/4.35    inference(rectify,[],[f3])).
% 31.56/4.35  fof(f3,axiom,(
% 31.56/4.35    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 31.56/4.35  fof(f12577,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) != k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f11830,plain,(
% 31.56/4.35    spl4_410 | ~spl4_4 | ~spl4_5 | ~spl4_407),
% 31.56/4.35    inference(avatar_split_clause,[],[f11795,f5089,f159,f154,f5106])).
% 31.56/4.35  fof(f159,plain,(
% 31.56/4.35    spl4_5 <=> v2_pre_topc(sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 31.56/4.35  fof(f11795,plain,(
% 31.56/4.35    v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_407)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f161,f156,f5091,f88])).
% 31.56/4.35  fof(f88,plain,(
% 31.56/4.35    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f43])).
% 31.56/4.35  fof(f43,plain,(
% 31.56/4.35    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.56/4.35    inference(flattening,[],[f42])).
% 31.56/4.35  fof(f42,plain,(
% 31.56/4.35    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.56/4.35    inference(ennf_transformation,[],[f22])).
% 31.56/4.35  fof(f22,axiom,(
% 31.56/4.35    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 31.56/4.35  fof(f161,plain,(
% 31.56/4.35    v2_pre_topc(sK0) | ~spl4_5),
% 31.56/4.35    inference(avatar_component_clause,[],[f159])).
% 31.56/4.35  fof(f11499,plain,(
% 31.56/4.35    spl4_525 | ~spl4_78 | ~spl4_123),
% 31.56/4.35    inference(avatar_split_clause,[],[f11498,f1323,f879,f8835])).
% 31.56/4.35  fof(f8835,plain,(
% 31.56/4.35    spl4_525 <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_525])])).
% 31.56/4.35  fof(f879,plain,(
% 31.56/4.35    spl4_78 <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 31.56/4.35  fof(f11498,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_78 | ~spl4_123)),
% 31.56/4.35    inference(forward_demodulation,[],[f11487,f881])).
% 31.56/4.35  fof(f881,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~spl4_78),
% 31.56/4.35    inference(avatar_component_clause,[],[f879])).
% 31.56/4.35  fof(f11487,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl4_123),
% 31.56/4.35    inference(superposition,[],[f113,f1325])).
% 31.56/4.35  fof(f11283,plain,(
% 31.56/4.35    spl4_353 | ~spl4_4 | ~spl4_319 | ~spl4_322),
% 31.56/4.35    inference(avatar_split_clause,[],[f11282,f3757,f3711,f154,f4153])).
% 31.56/4.35  fof(f4153,plain,(
% 31.56/4.35    spl4_353 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_353])])).
% 31.56/4.35  fof(f3711,plain,(
% 31.56/4.35    spl4_319 <=> v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_319])])).
% 31.56/4.35  fof(f3757,plain,(
% 31.56/4.35    spl4_322 <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).
% 31.56/4.35  fof(f11282,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_4 | ~spl4_319 | ~spl4_322)),
% 31.56/4.35    inference(subsumption_resolution,[],[f11281,f156])).
% 31.56/4.35  fof(f11281,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0) | (~spl4_319 | ~spl4_322)),
% 31.56/4.35    inference(subsumption_resolution,[],[f11246,f3713])).
% 31.56/4.35  fof(f3713,plain,(
% 31.56/4.35    v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~spl4_319),
% 31.56/4.35    inference(avatar_component_clause,[],[f3711])).
% 31.56/4.35  fof(f11246,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~l1_pre_topc(sK0) | ~spl4_322),
% 31.56/4.35    inference(resolution,[],[f3759,f75])).
% 31.56/4.35  fof(f3759,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_322),
% 31.56/4.35    inference(avatar_component_clause,[],[f3757])).
% 31.56/4.35  fof(f11197,plain,(
% 31.56/4.35    spl4_322 | ~spl4_135 | ~spl4_310),
% 31.56/4.35    inference(avatar_split_clause,[],[f11196,f3649,f1456,f3757])).
% 31.56/4.35  fof(f1456,plain,(
% 31.56/4.35    spl4_135 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).
% 31.56/4.35  fof(f3649,plain,(
% 31.56/4.35    spl4_310 <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).
% 31.56/4.35  fof(f11196,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_135 | ~spl4_310)),
% 31.56/4.35    inference(forward_demodulation,[],[f1458,f3651])).
% 31.56/4.35  fof(f3651,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_310),
% 31.56/4.35    inference(avatar_component_clause,[],[f3649])).
% 31.56/4.35  fof(f1458,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_135),
% 31.56/4.35    inference(avatar_component_clause,[],[f1456])).
% 31.56/4.35  fof(f11062,plain,(
% 31.56/4.35    sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | k1_xboole_0 != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k5_xboole_0(sK1,sK1) | sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) | k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 31.56/4.35    introduced(theory_tautology_sat_conflict,[])).
% 31.56/4.35  fof(f10845,plain,(
% 31.56/4.35    spl4_193 | ~spl4_124),
% 31.56/4.35    inference(avatar_split_clause,[],[f10844,f1328,f2393])).
% 31.56/4.35  fof(f2393,plain,(
% 31.56/4.35    spl4_193 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).
% 31.56/4.35  fof(f1328,plain,(
% 31.56/4.35    spl4_124 <=> r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).
% 31.56/4.35  fof(f10844,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl4_124),
% 31.56/4.35    inference(forward_demodulation,[],[f10840,f81])).
% 31.56/4.35  fof(f10840,plain,(
% 31.56/4.35    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) | ~spl4_124),
% 31.56/4.35    inference(resolution,[],[f1330,f114])).
% 31.56/4.35  fof(f1330,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | ~spl4_124),
% 31.56/4.35    inference(avatar_component_clause,[],[f1328])).
% 31.56/4.35  fof(f10761,plain,(
% 31.56/4.35    spl4_135 | ~spl4_4 | ~spl4_57),
% 31.56/4.35    inference(avatar_split_clause,[],[f10739,f689,f154,f1456])).
% 31.56/4.35  fof(f689,plain,(
% 31.56/4.35    spl4_57 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 31.56/4.35  fof(f10739,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_57)),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f156,f691,f89])).
% 31.56/4.35  fof(f691,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_57),
% 31.56/4.35    inference(avatar_component_clause,[],[f689])).
% 31.56/4.35  fof(f10733,plain,(
% 31.56/4.35    spl4_123 | ~spl4_60 | ~spl4_68),
% 31.56/4.35    inference(avatar_split_clause,[],[f10732,f765,f704,f1323])).
% 31.56/4.35  fof(f704,plain,(
% 31.56/4.35    spl4_60 <=> m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 31.56/4.35  fof(f765,plain,(
% 31.56/4.35    spl4_68 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 31.56/4.35  fof(f10732,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))) | (~spl4_60 | ~spl4_68)),
% 31.56/4.35    inference(forward_demodulation,[],[f10701,f767])).
% 31.56/4.35  fof(f767,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) | ~spl4_68),
% 31.56/4.35    inference(avatar_component_clause,[],[f765])).
% 31.56/4.35  fof(f10701,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))) | ~spl4_60),
% 31.56/4.35    inference(resolution,[],[f706,f115])).
% 31.56/4.35  fof(f706,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_60),
% 31.56/4.35    inference(avatar_component_clause,[],[f704])).
% 31.56/4.35  fof(f10731,plain,(
% 31.56/4.35    spl4_124 | ~spl4_60),
% 31.56/4.35    inference(avatar_split_clause,[],[f10700,f704,f1328])).
% 31.56/4.35  fof(f10700,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | ~spl4_60),
% 31.56/4.35    inference(resolution,[],[f706,f90])).
% 31.56/4.35  fof(f10672,plain,(
% 31.56/4.35    spl4_75 | ~spl4_59),
% 31.56/4.35    inference(avatar_split_clause,[],[f10671,f699,f834])).
% 31.56/4.35  fof(f699,plain,(
% 31.56/4.35    spl4_59 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 31.56/4.35  fof(f10671,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | ~spl4_59),
% 31.56/4.35    inference(forward_demodulation,[],[f10668,f81])).
% 31.56/4.35  fof(f10668,plain,(
% 31.56/4.35    k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) | ~spl4_59),
% 31.56/4.35    inference(resolution,[],[f701,f114])).
% 31.56/4.35  fof(f701,plain,(
% 31.56/4.35    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_59),
% 31.56/4.35    inference(avatar_component_clause,[],[f699])).
% 31.56/4.35  fof(f9410,plain,(
% 31.56/4.35    spl4_107 | ~spl4_19),
% 31.56/4.35    inference(avatar_split_clause,[],[f9384,f318,f1141])).
% 31.56/4.35  fof(f1141,plain,(
% 31.56/4.35    spl4_107 <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 31.56/4.35  fof(f318,plain,(
% 31.56/4.35    spl4_19 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 31.56/4.35  fof(f9384,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) | ~spl4_19),
% 31.56/4.35    inference(resolution,[],[f320,f115])).
% 31.56/4.35  fof(f320,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_19),
% 31.56/4.35    inference(avatar_component_clause,[],[f318])).
% 31.56/4.35  fof(f9294,plain,(
% 31.56/4.35    spl4_45 | ~spl4_21),
% 31.56/4.35    inference(avatar_split_clause,[],[f9293,f328,f543])).
% 31.56/4.35  fof(f543,plain,(
% 31.56/4.35    spl4_45 <=> k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 31.56/4.35  fof(f328,plain,(
% 31.56/4.35    spl4_21 <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 31.56/4.35  fof(f9293,plain,(
% 31.56/4.35    k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_21),
% 31.56/4.35    inference(forward_demodulation,[],[f9289,f81])).
% 31.56/4.35  fof(f9289,plain,(
% 31.56/4.35    k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))) | ~spl4_21),
% 31.56/4.35    inference(resolution,[],[f330,f114])).
% 31.56/4.35  fof(f330,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) | ~spl4_21),
% 31.56/4.35    inference(avatar_component_clause,[],[f328])).
% 31.56/4.35  fof(f9277,plain,(
% 31.56/4.35    spl4_20 | ~spl4_9),
% 31.56/4.35    inference(avatar_split_clause,[],[f9251,f216,f323])).
% 31.56/4.35  fof(f323,plain,(
% 31.56/4.35    spl4_20 <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 31.56/4.35  fof(f9251,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | ~spl4_9),
% 31.56/4.35    inference(resolution,[],[f218,f115])).
% 31.56/4.35  fof(f9276,plain,(
% 31.56/4.35    spl4_21 | ~spl4_9),
% 31.56/4.35    inference(avatar_split_clause,[],[f9250,f216,f328])).
% 31.56/4.35  fof(f9250,plain,(
% 31.56/4.35    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) | ~spl4_9),
% 31.56/4.35    inference(resolution,[],[f218,f90])).
% 31.56/4.35  fof(f9254,plain,(
% 31.56/4.35    spl4_19 | ~spl4_9),
% 31.56/4.35    inference(avatar_split_clause,[],[f9238,f216,f318])).
% 31.56/4.35  fof(f9238,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f218,f86])).
% 31.56/4.35  fof(f8267,plain,(
% 31.56/4.35    spl4_90 | ~spl4_3 | ~spl4_13),
% 31.56/4.35    inference(avatar_split_clause,[],[f8232,f236,f149,f970])).
% 31.56/4.35  fof(f970,plain,(
% 31.56/4.35    spl4_90 <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 31.56/4.35  fof(f236,plain,(
% 31.56/4.35    spl4_13 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 31.56/4.35  fof(f8232,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | (~spl4_3 | ~spl4_13)),
% 31.56/4.35    inference(superposition,[],[f815,f238])).
% 31.56/4.35  fof(f238,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl4_13),
% 31.56/4.35    inference(avatar_component_clause,[],[f236])).
% 31.56/4.35  fof(f815,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ) | ~spl4_3),
% 31.56/4.35    inference(forward_demodulation,[],[f810,f81])).
% 31.56/4.35  fof(f810,plain,(
% 31.56/4.35    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) ) | ~spl4_3),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f507,f114])).
% 31.56/4.35  fof(f507,plain,(
% 31.56/4.35    ( ! [X0] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f112,f181])).
% 31.56/4.35  fof(f8224,plain,(
% 31.56/4.35    spl4_369 | ~spl4_3 | ~spl4_368),
% 31.56/4.35    inference(avatar_split_clause,[],[f8219,f4435,f149,f4449])).
% 31.56/4.35  fof(f4449,plain,(
% 31.56/4.35    spl4_369 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_369])])).
% 31.56/4.35  fof(f8219,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl4_3 | ~spl4_368)),
% 31.56/4.35    inference(superposition,[],[f533,f4437])).
% 31.56/4.35  fof(f533,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) ) | ~spl4_3),
% 31.56/4.35    inference(forward_demodulation,[],[f500,f181])).
% 31.56/4.35  fof(f500,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))))) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f181,f113])).
% 31.56/4.35  fof(f7830,plain,(
% 31.56/4.35    spl4_363 | ~spl4_3 | ~spl4_13 | ~spl4_358),
% 31.56/4.35    inference(avatar_split_clause,[],[f7829,f4309,f236,f149,f4385])).
% 31.56/4.35  fof(f4385,plain,(
% 31.56/4.35    spl4_363 <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_363])])).
% 31.56/4.35  fof(f7829,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl4_3 | ~spl4_13 | ~spl4_358)),
% 31.56/4.35    inference(forward_demodulation,[],[f7806,f238])).
% 31.56/4.35  fof(f7806,plain,(
% 31.56/4.35    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl4_3 | ~spl4_358)),
% 31.56/4.35    inference(superposition,[],[f181,f4311])).
% 31.56/4.35  fof(f7116,plain,(
% 31.56/4.35    spl4_224 | ~spl4_117),
% 31.56/4.35    inference(avatar_split_clause,[],[f7112,f1212,f2701])).
% 31.56/4.35  fof(f2701,plain,(
% 31.56/4.35    spl4_224 <=> k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).
% 31.56/4.35  fof(f1212,plain,(
% 31.56/4.35    spl4_117 <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 31.56/4.35  fof(f7112,plain,(
% 31.56/4.35    k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))) | ~spl4_117),
% 31.56/4.35    inference(resolution,[],[f1214,f115])).
% 31.56/4.35  fof(f1214,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl4_117),
% 31.56/4.35    inference(avatar_component_clause,[],[f1212])).
% 31.56/4.35  fof(f6749,plain,(
% 31.56/4.35    spl4_237 | ~spl4_225),
% 31.56/4.35    inference(avatar_split_clause,[],[f6748,f2706,f2814])).
% 31.56/4.35  fof(f2814,plain,(
% 31.56/4.35    spl4_237 <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_237])])).
% 31.56/4.35  fof(f2706,plain,(
% 31.56/4.35    spl4_225 <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_225])])).
% 31.56/4.35  fof(f6748,plain,(
% 31.56/4.35    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) | ~spl4_225),
% 31.56/4.35    inference(forward_demodulation,[],[f6744,f81])).
% 31.56/4.35  fof(f6744,plain,(
% 31.56/4.35    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)) | ~spl4_225),
% 31.56/4.35    inference(resolution,[],[f2708,f114])).
% 31.56/4.35  fof(f2708,plain,(
% 31.56/4.35    r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) | ~spl4_225),
% 31.56/4.35    inference(avatar_component_clause,[],[f2706])).
% 31.56/4.35  fof(f6663,plain,(
% 31.56/4.35    spl4_145 | ~spl4_3 | ~spl4_13),
% 31.56/4.35    inference(avatar_split_clause,[],[f6655,f236,f149,f1584])).
% 31.56/4.35  fof(f1584,plain,(
% 31.56/4.35    spl4_145 <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).
% 31.56/4.35  fof(f6655,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_13)),
% 31.56/4.35    inference(superposition,[],[f533,f238])).
% 31.56/4.35  fof(f6587,plain,(
% 31.56/4.35    spl4_358 | ~spl4_3 | ~spl4_13),
% 31.56/4.35    inference(avatar_split_clause,[],[f6583,f236,f149,f4309])).
% 31.56/4.35  fof(f6583,plain,(
% 31.56/4.35    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_13)),
% 31.56/4.35    inference(superposition,[],[f4260,f238])).
% 31.56/4.35  fof(f4260,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) ) | ~spl4_3),
% 31.56/4.35    inference(backward_demodulation,[],[f508,f815])).
% 31.56/4.35  fof(f508,plain,(
% 31.56/4.35    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))))) ) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f113,f181])).
% 31.56/4.35  fof(f6437,plain,(
% 31.56/4.35    spl4_57 | ~spl4_30 | ~spl4_47),
% 31.56/4.35    inference(avatar_split_clause,[],[f6436,f590,f410,f689])).
% 31.56/4.35  fof(f410,plain,(
% 31.56/4.35    spl4_30 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 31.56/4.35  fof(f590,plain,(
% 31.56/4.35    spl4_47 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 31.56/4.35  fof(f6436,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_30 | ~spl4_47)),
% 31.56/4.35    inference(forward_demodulation,[],[f412,f592])).
% 31.56/4.35  fof(f592,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl4_47),
% 31.56/4.35    inference(avatar_component_clause,[],[f590])).
% 31.56/4.35  fof(f412,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_30),
% 31.56/4.35    inference(avatar_component_clause,[],[f410])).
% 31.56/4.35  fof(f6255,plain,(
% 31.56/4.35    spl4_60 | ~spl4_33 | ~spl4_47),
% 31.56/4.35    inference(avatar_split_clause,[],[f6254,f590,f425,f704])).
% 31.56/4.35  fof(f425,plain,(
% 31.56/4.35    spl4_33 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 31.56/4.35  fof(f6254,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_33 | ~spl4_47)),
% 31.56/4.35    inference(forward_demodulation,[],[f427,f592])).
% 31.56/4.35  fof(f427,plain,(
% 31.56/4.35    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_33),
% 31.56/4.35    inference(avatar_component_clause,[],[f425])).
% 31.56/4.35  fof(f6144,plain,(
% 31.56/4.35    spl4_61 | ~spl4_34 | ~spl4_47),
% 31.56/4.35    inference(avatar_split_clause,[],[f6143,f590,f430,f709])).
% 31.56/4.35  fof(f709,plain,(
% 31.56/4.35    spl4_61 <=> v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 31.56/4.35  fof(f430,plain,(
% 31.56/4.35    spl4_34 <=> v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 31.56/4.35  fof(f6143,plain,(
% 31.56/4.35    v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0) | (~spl4_34 | ~spl4_47)),
% 31.56/4.35    inference(forward_demodulation,[],[f432,f592])).
% 31.56/4.35  fof(f432,plain,(
% 31.56/4.35    v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~spl4_34),
% 31.56/4.35    inference(avatar_component_clause,[],[f430])).
% 31.56/4.35  fof(f6142,plain,(
% 31.56/4.35    spl4_78 | ~spl4_70),
% 31.56/4.35    inference(avatar_split_clause,[],[f6119,f783,f879])).
% 31.56/4.35  fof(f783,plain,(
% 31.56/4.35    spl4_70 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 31.56/4.35  fof(f6119,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~spl4_70),
% 31.56/4.35    inference(resolution,[],[f785,f115])).
% 31.56/4.35  fof(f785,plain,(
% 31.56/4.35    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_70),
% 31.56/4.35    inference(avatar_component_clause,[],[f783])).
% 31.56/4.35  fof(f6138,plain,(
% 31.56/4.35    spl4_82 | ~spl4_4 | ~spl4_70),
% 31.56/4.35    inference(avatar_split_clause,[],[f6137,f783,f154,f899])).
% 31.56/4.35  fof(f899,plain,(
% 31.56/4.35    spl4_82 <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 31.56/4.35  fof(f6137,plain,(
% 31.56/4.35    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) | (~spl4_4 | ~spl4_70)),
% 31.56/4.35    inference(subsumption_resolution,[],[f6110,f156])).
% 31.56/4.35  fof(f6110,plain,(
% 31.56/4.35    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl4_70),
% 31.56/4.35    inference(resolution,[],[f785,f74])).
% 31.56/4.35  fof(f74,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f35])).
% 31.56/4.35  fof(f35,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(ennf_transformation,[],[f23])).
% 31.56/4.35  fof(f23,axiom,(
% 31.56/4.35    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 31.56/4.35  fof(f6136,plain,(
% 31.56/4.35    spl4_83 | ~spl4_4 | ~spl4_70),
% 31.56/4.35    inference(avatar_split_clause,[],[f6135,f783,f154,f904])).
% 31.56/4.35  fof(f904,plain,(
% 31.56/4.35    spl4_83 <=> k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 31.56/4.35  fof(f6135,plain,(
% 31.56/4.35    k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | (~spl4_4 | ~spl4_70)),
% 31.56/4.35    inference(subsumption_resolution,[],[f6109,f156])).
% 31.56/4.35  fof(f6109,plain,(
% 31.56/4.35    k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | ~spl4_70),
% 31.56/4.35    inference(resolution,[],[f785,f73])).
% 31.56/4.35  fof(f73,plain,(
% 31.56/4.35    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.35    inference(cnf_transformation,[],[f34])).
% 31.56/4.35  fof(f34,plain,(
% 31.56/4.35    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.35    inference(ennf_transformation,[],[f21])).
% 31.56/4.35  fof(f21,axiom,(
% 31.56/4.35    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 31.56/4.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 31.56/4.35  fof(f6070,plain,(
% 31.56/4.35    spl4_118 | ~spl4_91),
% 31.56/4.35    inference(avatar_split_clause,[],[f6066,f975,f1217])).
% 31.56/4.35  fof(f1217,plain,(
% 31.56/4.35    spl4_118 <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 31.56/4.35  fof(f975,plain,(
% 31.56/4.35    spl4_91 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 31.56/4.35  fof(f6066,plain,(
% 31.56/4.35    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) | ~spl4_91),
% 31.56/4.35    inference(resolution,[],[f977,f115])).
% 31.56/4.35  fof(f977,plain,(
% 31.56/4.35    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl4_91),
% 31.56/4.35    inference(avatar_component_clause,[],[f975])).
% 31.56/4.35  fof(f6068,plain,(
% 31.56/4.35    spl4_117 | ~spl4_91),
% 31.56/4.35    inference(avatar_split_clause,[],[f6063,f975,f1212])).
% 31.56/4.35  fof(f6063,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl4_91),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f977,f86])).
% 31.56/4.35  fof(f6036,plain,(
% 31.56/4.35    spl4_59 | ~spl4_32 | ~spl4_47),
% 31.56/4.35    inference(avatar_split_clause,[],[f6035,f590,f420,f699])).
% 31.56/4.35  fof(f420,plain,(
% 31.56/4.35    spl4_32 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 31.56/4.35  fof(f6035,plain,(
% 31.56/4.35    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl4_32 | ~spl4_47)),
% 31.56/4.35    inference(forward_demodulation,[],[f422,f592])).
% 31.56/4.35  fof(f422,plain,(
% 31.56/4.35    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_32),
% 31.56/4.35    inference(avatar_component_clause,[],[f420])).
% 31.56/4.35  fof(f5968,plain,(
% 31.56/4.35    ~spl4_60 | spl4_70 | ~spl4_68),
% 31.56/4.35    inference(avatar_split_clause,[],[f5964,f765,f783,f704])).
% 31.56/4.35  fof(f5964,plain,(
% 31.56/4.35    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_68),
% 31.56/4.35    inference(superposition,[],[f86,f767])).
% 31.56/4.35  fof(f5958,plain,(
% 31.56/4.35    spl4_68 | ~spl4_12 | ~spl4_47),
% 31.56/4.35    inference(avatar_split_clause,[],[f5957,f590,f231,f765])).
% 31.56/4.35  fof(f231,plain,(
% 31.56/4.35    spl4_12 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 31.56/4.35  fof(f5957,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) | (~spl4_12 | ~spl4_47)),
% 31.56/4.35    inference(forward_demodulation,[],[f233,f592])).
% 31.56/4.35  fof(f233,plain,(
% 31.56/4.35    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl4_12),
% 31.56/4.35    inference(avatar_component_clause,[],[f231])).
% 31.56/4.35  fof(f5944,plain,(
% 31.56/4.35    spl4_91 | ~spl4_73),
% 31.56/4.35    inference(avatar_split_clause,[],[f5938,f818,f975])).
% 31.56/4.35  fof(f818,plain,(
% 31.56/4.35    spl4_73 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 31.56/4.35  fof(f5938,plain,(
% 31.56/4.35    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl4_73),
% 31.56/4.35    inference(unit_resulting_resolution,[],[f820,f91])).
% 31.56/4.35  fof(f820,plain,(
% 31.56/4.35    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_73),
% 31.56/4.35    inference(avatar_component_clause,[],[f818])).
% 31.56/4.35  fof(f5936,plain,(
% 31.56/4.35    spl4_44 | ~spl4_3),
% 31.56/4.35    inference(avatar_split_clause,[],[f5919,f149,f529])).
% 31.56/4.35  fof(f5919,plain,(
% 31.56/4.35    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f110,f181])).
% 31.56/4.35  fof(f5933,plain,(
% 31.56/4.35    spl4_43 | ~spl4_3),
% 31.56/4.35    inference(avatar_split_clause,[],[f5907,f149,f524])).
% 31.56/4.35  fof(f524,plain,(
% 31.56/4.35    spl4_43 <=> k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1)),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 31.56/4.35  fof(f5907,plain,(
% 31.56/4.35    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) | ~spl4_3),
% 31.56/4.35    inference(superposition,[],[f181,f111])).
% 31.56/4.35  fof(f5805,plain,(
% 31.56/4.35    spl4_31 | ~spl4_6),
% 31.56/4.35    inference(avatar_split_clause,[],[f5780,f200,f415])).
% 31.56/4.35  fof(f415,plain,(
% 31.56/4.35    spl4_31 <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 31.56/4.35  fof(f200,plain,(
% 31.56/4.35    spl4_6 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.35    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 31.56/4.35  fof(f5780,plain,(
% 31.56/4.35    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl4_6),
% 31.56/4.35    inference(resolution,[],[f202,f115])).
% 31.56/4.35  fof(f202,plain,(
% 31.56/4.35    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 31.56/4.35    inference(avatar_component_clause,[],[f200])).
% 31.56/4.35  fof(f5804,plain,(
% 31.56/4.35    spl4_32 | ~spl4_6),
% 31.56/4.35    inference(avatar_split_clause,[],[f5779,f200,f420])).
% 31.56/4.35  fof(f5779,plain,(
% 31.56/4.35    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_6),
% 31.56/4.35    inference(resolution,[],[f202,f90])).
% 31.56/4.35  fof(f5800,plain,(
% 31.56/4.35    ~spl4_39 | spl4_40 | ~spl4_4 | ~spl4_6),
% 31.56/4.35    inference(avatar_split_clause,[],[f5799,f200,f154,f468,f464])).
% 31.56/4.36  fof(f464,plain,(
% 31.56/4.36    spl4_39 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 31.56/4.36    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 31.56/4.36  fof(f468,plain,(
% 31.56/4.36    spl4_40 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 31.56/4.36    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 31.56/4.36  fof(f5799,plain,(
% 31.56/4.36    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl4_4 | ~spl4_6)),
% 31.56/4.36    inference(subsumption_resolution,[],[f5772,f156])).
% 31.56/4.36  fof(f5772,plain,(
% 31.56/4.36    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_6),
% 31.56/4.36    inference(resolution,[],[f202,f75])).
% 31.56/4.36  fof(f5796,plain,(
% 31.56/4.36    spl4_36 | ~spl4_4 | ~spl4_6),
% 31.56/4.36    inference(avatar_split_clause,[],[f5795,f200,f154,f440])).
% 31.56/4.36  fof(f440,plain,(
% 31.56/4.36    spl4_36 <=> k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))),
% 31.56/4.36    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 31.56/4.36  fof(f5795,plain,(
% 31.56/4.36    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl4_4 | ~spl4_6)),
% 31.56/4.36    inference(subsumption_resolution,[],[f5770,f156])).
% 31.56/4.36  fof(f5770,plain,(
% 31.56/4.36    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0) | ~spl4_6),
% 31.56/4.36    inference(resolution,[],[f202,f73])).
% 31.56/4.36  fof(f5792,plain,(
% 31.56/4.36    spl4_38 | ~spl4_4 | ~spl4_6),
% 31.56/4.36    inference(avatar_split_clause,[],[f5791,f200,f154,f450])).
% 31.56/4.36  fof(f450,plain,(
% 31.56/4.36    spl4_38 <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))),
% 31.56/4.36    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 31.56/4.36  fof(f5791,plain,(
% 31.56/4.36    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl4_4 | ~spl4_6)),
% 31.56/4.36    inference(subsumption_resolution,[],[f5768,f156])).
% 31.56/4.36  fof(f5768,plain,(
% 31.56/4.36    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_6),
% 31.56/4.36    inference(resolution,[],[f202,f71])).
% 31.56/4.37  fof(f71,plain,(
% 31.56/4.37    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.56/4.37    inference(cnf_transformation,[],[f32])).
% 31.56/4.37  fof(f32,plain,(
% 31.56/4.37    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.56/4.37    inference(ennf_transformation,[],[f25])).
% 31.56/4.37  fof(f25,axiom,(
% 31.56/4.37    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 31.56/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 31.56/4.37  fof(f5786,plain,(
% 31.56/4.37    spl4_34 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 31.56/4.37    inference(avatar_split_clause,[],[f5762,f200,f159,f154,f430])).
% 31.56/4.37  fof(f5762,plain,(
% 31.56/4.37    v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_6)),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f161,f156,f202,f88])).
% 31.56/4.37  fof(f5785,plain,(
% 31.56/4.37    spl4_33 | ~spl4_4 | ~spl4_6),
% 31.56/4.37    inference(avatar_split_clause,[],[f5763,f200,f154,f425])).
% 31.56/4.37  fof(f5763,plain,(
% 31.56/4.37    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_6)),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f156,f202,f89])).
% 31.56/4.37  fof(f5782,plain,(
% 31.56/4.37    spl4_30 | ~spl4_6),
% 31.56/4.37    inference(avatar_split_clause,[],[f5767,f200,f410])).
% 31.56/4.37  fof(f5767,plain,(
% 31.56/4.37    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f202,f86])).
% 31.56/4.37  fof(f5700,plain,(
% 31.56/4.37    spl4_18 | ~spl4_8),
% 31.56/4.37    inference(avatar_split_clause,[],[f5698,f211,f285])).
% 31.56/4.37  fof(f211,plain,(
% 31.56/4.37    spl4_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 31.56/4.37  fof(f5698,plain,(
% 31.56/4.37    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl4_8),
% 31.56/4.37    inference(resolution,[],[f213,f114])).
% 31.56/4.37  fof(f213,plain,(
% 31.56/4.37    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_8),
% 31.56/4.37    inference(avatar_component_clause,[],[f211])).
% 31.56/4.37  fof(f5694,plain,(
% 31.56/4.37    spl4_76 | ~spl4_74),
% 31.56/4.37    inference(avatar_split_clause,[],[f5690,f824,f845])).
% 31.56/4.37  fof(f824,plain,(
% 31.56/4.37    spl4_74 <=> r1_tarski(sK1,sK1)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 31.56/4.37  fof(f5690,plain,(
% 31.56/4.37    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_74),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f826,f91])).
% 31.56/4.37  fof(f826,plain,(
% 31.56/4.37    r1_tarski(sK1,sK1) | ~spl4_74),
% 31.56/4.37    inference(avatar_component_clause,[],[f824])).
% 31.56/4.37  fof(f5682,plain,(
% 31.56/4.37    spl4_7 | ~spl4_3),
% 31.56/4.37    inference(avatar_split_clause,[],[f5681,f149,f206])).
% 31.56/4.37  fof(f206,plain,(
% 31.56/4.37    spl4_7 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 31.56/4.37  fof(f5681,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl4_3),
% 31.56/4.37    inference(forward_demodulation,[],[f5655,f81])).
% 31.56/4.37  fof(f5655,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) | ~spl4_3),
% 31.56/4.37    inference(resolution,[],[f151,f115])).
% 31.56/4.37  fof(f5680,plain,(
% 31.56/4.37    spl4_8 | ~spl4_3),
% 31.56/4.37    inference(avatar_split_clause,[],[f5654,f149,f211])).
% 31.56/4.37  fof(f5654,plain,(
% 31.56/4.37    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 31.56/4.37    inference(resolution,[],[f151,f90])).
% 31.56/4.37  fof(f5672,plain,(
% 31.56/4.37    spl4_12 | ~spl4_3 | ~spl4_4),
% 31.56/4.37    inference(avatar_split_clause,[],[f5671,f154,f149,f231])).
% 31.56/4.37  fof(f5671,plain,(
% 31.56/4.37    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl4_3 | ~spl4_4)),
% 31.56/4.37    inference(subsumption_resolution,[],[f5645,f156])).
% 31.56/4.37  fof(f5645,plain,(
% 31.56/4.37    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_3),
% 31.56/4.37    inference(resolution,[],[f151,f73])).
% 31.56/4.37  fof(f5670,plain,(
% 31.56/4.37    spl4_13 | ~spl4_3 | ~spl4_4),
% 31.56/4.37    inference(avatar_split_clause,[],[f5669,f154,f149,f236])).
% 31.56/4.37  fof(f5669,plain,(
% 31.56/4.37    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_4)),
% 31.56/4.37    inference(subsumption_resolution,[],[f5644,f156])).
% 31.56/4.37  fof(f5644,plain,(
% 31.56/4.37    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 31.56/4.37    inference(resolution,[],[f151,f72])).
% 31.56/4.37  fof(f5668,plain,(
% 31.56/4.37    spl4_14 | ~spl4_3 | ~spl4_4),
% 31.56/4.37    inference(avatar_split_clause,[],[f5667,f154,f149,f241])).
% 31.56/4.37  fof(f241,plain,(
% 31.56/4.37    spl4_14 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 31.56/4.37  fof(f5667,plain,(
% 31.56/4.37    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl4_3 | ~spl4_4)),
% 31.56/4.37    inference(subsumption_resolution,[],[f5643,f156])).
% 31.56/4.37  fof(f5643,plain,(
% 31.56/4.37    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 31.56/4.37    inference(resolution,[],[f151,f71])).
% 31.56/4.37  fof(f5662,plain,(
% 31.56/4.37    spl4_10 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 31.56/4.37    inference(avatar_split_clause,[],[f5637,f159,f154,f149,f221])).
% 31.56/4.37  fof(f221,plain,(
% 31.56/4.37    spl4_10 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 31.56/4.37  fof(f5637,plain,(
% 31.56/4.37    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f161,f156,f151,f88])).
% 31.56/4.37  fof(f5661,plain,(
% 31.56/4.37    spl4_9 | ~spl4_3 | ~spl4_4),
% 31.56/4.37    inference(avatar_split_clause,[],[f5638,f154,f149,f216])).
% 31.56/4.37  fof(f5638,plain,(
% 31.56/4.37    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_4)),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f156,f151,f89])).
% 31.56/4.37  fof(f5657,plain,(
% 31.56/4.37    spl4_6 | ~spl4_3),
% 31.56/4.37    inference(avatar_split_clause,[],[f5642,f149,f200])).
% 31.56/4.37  fof(f5642,plain,(
% 31.56/4.37    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f151,f86])).
% 31.56/4.37  fof(f4438,plain,(
% 31.56/4.37    spl4_368 | ~spl4_145 | ~spl4_358),
% 31.56/4.37    inference(avatar_split_clause,[],[f4433,f4309,f1584,f4435])).
% 31.56/4.37  fof(f4433,plain,(
% 31.56/4.37    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl4_145 | ~spl4_358)),
% 31.56/4.37    inference(forward_demodulation,[],[f1586,f4311])).
% 31.56/4.37  fof(f1586,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl4_145),
% 31.56/4.37    inference(avatar_component_clause,[],[f1584])).
% 31.56/4.37  fof(f3714,plain,(
% 31.56/4.37    spl4_319 | ~spl4_165 | ~spl4_310),
% 31.56/4.37    inference(avatar_split_clause,[],[f3673,f3649,f1921,f3711])).
% 31.56/4.37  fof(f1921,plain,(
% 31.56/4.37    spl4_165 <=> v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_165])])).
% 31.56/4.37  fof(f3673,plain,(
% 31.56/4.37    v4_pre_topc(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | (~spl4_165 | ~spl4_310)),
% 31.56/4.37    inference(backward_demodulation,[],[f1923,f3651])).
% 31.56/4.37  fof(f1923,plain,(
% 31.56/4.37    v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~spl4_165),
% 31.56/4.37    inference(avatar_component_clause,[],[f1921])).
% 31.56/4.37  fof(f3652,plain,(
% 31.56/4.37    spl4_310 | ~spl4_58 | ~spl4_75),
% 31.56/4.37    inference(avatar_split_clause,[],[f3622,f834,f694,f3649])).
% 31.56/4.37  fof(f694,plain,(
% 31.56/4.37    spl4_58 <=> k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 31.56/4.37  fof(f3622,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_58 | ~spl4_75)),
% 31.56/4.37    inference(backward_demodulation,[],[f696,f836])).
% 31.56/4.37  fof(f696,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl4_58),
% 31.56/4.37    inference(avatar_component_clause,[],[f694])).
% 31.56/4.37  fof(f2710,plain,(
% 31.56/4.37    spl4_225 | ~spl4_117),
% 31.56/4.37    inference(avatar_split_clause,[],[f2692,f1212,f2706])).
% 31.56/4.37  fof(f2692,plain,(
% 31.56/4.37    r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) | ~spl4_117),
% 31.56/4.37    inference(resolution,[],[f1214,f90])).
% 31.56/4.37  fof(f1946,plain,(
% 31.56/4.37    spl4_167 | ~spl4_162),
% 31.56/4.37    inference(avatar_split_clause,[],[f1945,f1849,f1936])).
% 31.56/4.37  fof(f1849,plain,(
% 31.56/4.37    spl4_162 <=> r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).
% 31.56/4.37  fof(f1945,plain,(
% 31.56/4.37    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_162),
% 31.56/4.37    inference(forward_demodulation,[],[f1933,f109])).
% 31.56/4.37  fof(f109,plain,(
% 31.56/4.37    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 31.56/4.37    inference(definition_unfolding,[],[f69,f82])).
% 31.56/4.37  fof(f69,plain,(
% 31.56/4.37    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 31.56/4.37    inference(cnf_transformation,[],[f8])).
% 31.56/4.37  fof(f8,axiom,(
% 31.56/4.37    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 31.56/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 31.56/4.37  fof(f1933,plain,(
% 31.56/4.37    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)) | ~spl4_162),
% 31.56/4.37    inference(resolution,[],[f1851,f114])).
% 31.56/4.37  fof(f1851,plain,(
% 31.56/4.37    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl4_162),
% 31.56/4.37    inference(avatar_component_clause,[],[f1849])).
% 31.56/4.37  fof(f1924,plain,(
% 31.56/4.37    ~spl4_135 | spl4_165 | ~spl4_4 | ~spl4_61 | ~spl4_63),
% 31.56/4.37    inference(avatar_split_clause,[],[f1919,f719,f709,f154,f1921,f1456])).
% 31.56/4.37  fof(f719,plain,(
% 31.56/4.37    spl4_63 <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 31.56/4.37  fof(f1919,plain,(
% 31.56/4.37    v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_61 | ~spl4_63)),
% 31.56/4.37    inference(subsumption_resolution,[],[f1918,f156])).
% 31.56/4.37  fof(f1918,plain,(
% 31.56/4.37    v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_61 | ~spl4_63)),
% 31.56/4.37    inference(subsumption_resolution,[],[f1914,f711])).
% 31.56/4.37  fof(f711,plain,(
% 31.56/4.37    v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0) | ~spl4_61),
% 31.56/4.37    inference(avatar_component_clause,[],[f709])).
% 31.56/4.37  fof(f1914,plain,(
% 31.56/4.37    ~v3_pre_topc(k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),sK0) | v4_pre_topc(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_63),
% 31.56/4.37    inference(superposition,[],[f78,f721])).
% 31.56/4.37  fof(f721,plain,(
% 31.56/4.37    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl4_63),
% 31.56/4.37    inference(avatar_component_clause,[],[f719])).
% 31.56/4.37  fof(f1887,plain,(
% 31.56/4.37    spl4_164 | ~spl4_58),
% 31.56/4.37    inference(avatar_split_clause,[],[f1874,f694,f1884])).
% 31.56/4.37  fof(f1884,plain,(
% 31.56/4.37    spl4_164 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).
% 31.56/4.37  fof(f1874,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))))) | ~spl4_58),
% 31.56/4.37    inference(superposition,[],[f113,f696])).
% 31.56/4.37  fof(f1864,plain,(
% 31.56/4.37    spl4_63 | ~spl4_36 | ~spl4_47),
% 31.56/4.37    inference(avatar_split_clause,[],[f1863,f590,f440,f719])).
% 31.56/4.37  fof(f1863,plain,(
% 31.56/4.37    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_36 | ~spl4_47)),
% 31.56/4.37    inference(forward_demodulation,[],[f442,f592])).
% 31.56/4.37  fof(f442,plain,(
% 31.56/4.37    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl4_36),
% 31.56/4.37    inference(avatar_component_clause,[],[f440])).
% 31.56/4.37  fof(f1852,plain,(
% 31.56/4.37    spl4_162 | ~spl4_150),
% 31.56/4.37    inference(avatar_split_clause,[],[f1827,f1659,f1849])).
% 31.56/4.37  fof(f1827,plain,(
% 31.56/4.37    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl4_150),
% 31.56/4.37    inference(superposition,[],[f112,f1661])).
% 31.56/4.37  fof(f1821,plain,(
% 31.56/4.37    spl4_58 | ~spl4_31 | ~spl4_47),
% 31.56/4.37    inference(avatar_split_clause,[],[f1820,f590,f415,f694])).
% 31.56/4.37  fof(f1820,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_31 | ~spl4_47)),
% 31.56/4.37    inference(forward_demodulation,[],[f417,f592])).
% 31.56/4.37  fof(f417,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl4_31),
% 31.56/4.37    inference(avatar_component_clause,[],[f415])).
% 31.56/4.37  fof(f1734,plain,(
% 31.56/4.37    spl4_156 | ~spl4_20),
% 31.56/4.37    inference(avatar_split_clause,[],[f1721,f323,f1731])).
% 31.56/4.37  fof(f1731,plain,(
% 31.56/4.37    spl4_156 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).
% 31.56/4.37  fof(f1721,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) | ~spl4_20),
% 31.56/4.37    inference(superposition,[],[f113,f325])).
% 31.56/4.37  fof(f325,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | ~spl4_20),
% 31.56/4.37    inference(avatar_component_clause,[],[f323])).
% 31.56/4.37  fof(f1668,plain,(
% 31.56/4.37    spl4_150 | ~spl4_147),
% 31.56/4.37    inference(avatar_split_clause,[],[f1657,f1610,f1659])).
% 31.56/4.37  fof(f1610,plain,(
% 31.56/4.37    spl4_147 <=> r1_tarski(k1_xboole_0,sK1)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).
% 31.56/4.37  fof(f1657,plain,(
% 31.56/4.37    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) | ~spl4_147),
% 31.56/4.37    inference(resolution,[],[f1612,f114])).
% 31.56/4.37  fof(f1612,plain,(
% 31.56/4.37    r1_tarski(k1_xboole_0,sK1) | ~spl4_147),
% 31.56/4.37    inference(avatar_component_clause,[],[f1610])).
% 31.56/4.37  fof(f1653,plain,(
% 31.56/4.37    spl4_50 | ~spl4_3 | ~spl4_43),
% 31.56/4.37    inference(avatar_split_clause,[],[f1652,f524,f149,f605])).
% 31.56/4.37  fof(f605,plain,(
% 31.56/4.37    spl4_50 <=> sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1))))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 31.56/4.37  fof(f1652,plain,(
% 31.56/4.37    sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) | (~spl4_3 | ~spl4_43)),
% 31.56/4.37    inference(forward_demodulation,[],[f1617,f111])).
% 31.56/4.37  fof(f1617,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(sK1,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) | (~spl4_3 | ~spl4_43)),
% 31.56/4.37    inference(superposition,[],[f508,f526])).
% 31.56/4.37  fof(f526,plain,(
% 31.56/4.37    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) | ~spl4_43),
% 31.56/4.37    inference(avatar_component_clause,[],[f524])).
% 31.56/4.37  fof(f1646,plain,(
% 31.56/4.37    spl4_148 | ~spl4_3 | ~spl4_44),
% 31.56/4.37    inference(avatar_split_clause,[],[f1641,f529,f149,f1643])).
% 31.56/4.37  fof(f1641,plain,(
% 31.56/4.37    k1_xboole_0 = k5_xboole_0(sK1,sK1) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(forward_demodulation,[],[f1640,f109])).
% 31.56/4.37  fof(f1640,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK1) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(forward_demodulation,[],[f1614,f111])).
% 31.56/4.37  fof(f1614,plain,(
% 31.56/4.37    k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(superposition,[],[f508,f531])).
% 31.56/4.37  fof(f1613,plain,(
% 31.56/4.37    spl4_147 | ~spl4_3),
% 31.56/4.37    inference(avatar_split_clause,[],[f1601,f149,f1610])).
% 31.56/4.37  fof(f1601,plain,(
% 31.56/4.37    r1_tarski(k1_xboole_0,sK1) | ~spl4_3),
% 31.56/4.37    inference(superposition,[],[f1576,f109])).
% 31.56/4.37  fof(f1576,plain,(
% 31.56/4.37    ( ! [X4] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X4)),sK1)) ) | ~spl4_3),
% 31.56/4.37    inference(superposition,[],[f507,f533])).
% 31.56/4.37  fof(f1582,plain,(
% 31.56/4.37    spl4_144 | ~spl4_3 | ~spl4_44),
% 31.56/4.37    inference(avatar_split_clause,[],[f1577,f529,f149,f1579])).
% 31.56/4.37  fof(f1577,plain,(
% 31.56/4.37    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(forward_demodulation,[],[f1569,f109])).
% 31.56/4.37  fof(f1569,plain,(
% 31.56/4.37    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(superposition,[],[f533,f531])).
% 31.56/4.37  fof(f827,plain,(
% 31.56/4.37    spl4_74 | ~spl4_3 | ~spl4_44),
% 31.56/4.37    inference(avatar_split_clause,[],[f822,f529,f149,f824])).
% 31.56/4.37  fof(f822,plain,(
% 31.56/4.37    r1_tarski(sK1,sK1) | (~spl4_3 | ~spl4_44)),
% 31.56/4.37    inference(superposition,[],[f507,f531])).
% 31.56/4.37  fof(f821,plain,(
% 31.56/4.37    spl4_73 | ~spl4_3 | ~spl4_13),
% 31.56/4.37    inference(avatar_split_clause,[],[f813,f236,f149,f818])).
% 31.56/4.37  fof(f813,plain,(
% 31.56/4.37    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_3 | ~spl4_13)),
% 31.56/4.37    inference(superposition,[],[f507,f238])).
% 31.56/4.37  fof(f806,plain,(
% 31.56/4.37    spl4_72 | ~spl4_56),
% 31.56/4.37    inference(avatar_split_clause,[],[f794,f658,f802])).
% 31.56/4.37  fof(f802,plain,(
% 31.56/4.37    spl4_72 <=> k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 31.56/4.37  fof(f658,plain,(
% 31.56/4.37    spl4_56 <=> m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 31.56/4.37  fof(f794,plain,(
% 31.56/4.37    k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,sK1)))) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) | ~spl4_56),
% 31.56/4.37    inference(resolution,[],[f660,f115])).
% 31.56/4.37  fof(f660,plain,(
% 31.56/4.37    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl4_56),
% 31.56/4.37    inference(avatar_component_clause,[],[f658])).
% 31.56/4.37  fof(f661,plain,(
% 31.56/4.37    spl4_56 | ~spl4_49),
% 31.56/4.37    inference(avatar_split_clause,[],[f647,f600,f658])).
% 31.56/4.37  fof(f600,plain,(
% 31.56/4.37    spl4_49 <=> r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 31.56/4.37  fof(f647,plain,(
% 31.56/4.37    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl4_49),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f602,f91])).
% 31.56/4.37  fof(f602,plain,(
% 31.56/4.37    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | ~spl4_49),
% 31.56/4.37    inference(avatar_component_clause,[],[f600])).
% 31.56/4.37  fof(f603,plain,(
% 31.56/4.37    spl4_49 | ~spl4_18),
% 31.56/4.37    inference(avatar_split_clause,[],[f569,f285,f600])).
% 31.56/4.37  fof(f569,plain,(
% 31.56/4.37    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | ~spl4_18),
% 31.56/4.37    inference(superposition,[],[f112,f287])).
% 31.56/4.37  fof(f593,plain,(
% 31.56/4.37    spl4_47 | ~spl4_7 | ~spl4_18),
% 31.56/4.37    inference(avatar_split_clause,[],[f564,f285,f206,f590])).
% 31.56/4.37  fof(f564,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | (~spl4_7 | ~spl4_18)),
% 31.56/4.37    inference(backward_demodulation,[],[f208,f287])).
% 31.56/4.37  fof(f208,plain,(
% 31.56/4.37    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl4_7),
% 31.56/4.37    inference(avatar_component_clause,[],[f206])).
% 31.56/4.37  fof(f558,plain,(
% 31.56/4.37    ~spl4_46 | ~spl4_4 | ~spl4_6 | spl4_39),
% 31.56/4.37    inference(avatar_split_clause,[],[f549,f464,f200,f154,f555])).
% 31.56/4.37  fof(f555,plain,(
% 31.56/4.37    spl4_46 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 31.56/4.37  fof(f549,plain,(
% 31.56/4.37    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl4_4 | ~spl4_6 | spl4_39)),
% 31.56/4.37    inference(unit_resulting_resolution,[],[f156,f202,f466,f78])).
% 31.56/4.37  fof(f466,plain,(
% 31.56/4.37    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl4_39),
% 31.56/4.37    inference(avatar_component_clause,[],[f464])).
% 31.56/4.37  fof(f162,plain,(
% 31.56/4.37    spl4_5),
% 31.56/4.37    inference(avatar_split_clause,[],[f64,f159])).
% 31.56/4.37  fof(f64,plain,(
% 31.56/4.37    v2_pre_topc(sK0)),
% 31.56/4.37    inference(cnf_transformation,[],[f51])).
% 31.56/4.37  fof(f51,plain,(
% 31.56/4.37    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 31.56/4.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 31.56/4.37  fof(f49,plain,(
% 31.56/4.37    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 31.56/4.37    introduced(choice_axiom,[])).
% 31.56/4.37  fof(f50,plain,(
% 31.56/4.37    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 31.56/4.37    introduced(choice_axiom,[])).
% 31.56/4.37  fof(f48,plain,(
% 31.56/4.37    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.56/4.37    inference(flattening,[],[f47])).
% 31.56/4.37  fof(f47,plain,(
% 31.56/4.37    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.56/4.37    inference(nnf_transformation,[],[f31])).
% 31.56/4.37  fof(f31,plain,(
% 31.56/4.37    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.56/4.37    inference(flattening,[],[f30])).
% 31.56/4.37  fof(f30,plain,(
% 31.56/4.37    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.56/4.37    inference(ennf_transformation,[],[f28])).
% 31.56/4.37  fof(f28,negated_conjecture,(
% 31.56/4.37    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 31.56/4.37    inference(negated_conjecture,[],[f27])).
% 31.56/4.37  fof(f27,conjecture,(
% 31.56/4.37    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 31.56/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 31.56/4.37  fof(f157,plain,(
% 31.56/4.37    spl4_4),
% 31.56/4.37    inference(avatar_split_clause,[],[f65,f154])).
% 31.56/4.37  fof(f65,plain,(
% 31.56/4.37    l1_pre_topc(sK0)),
% 31.56/4.37    inference(cnf_transformation,[],[f51])).
% 31.56/4.37  fof(f152,plain,(
% 31.56/4.37    spl4_3),
% 31.56/4.37    inference(avatar_split_clause,[],[f66,f149])).
% 31.56/4.37  fof(f66,plain,(
% 31.56/4.37    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.56/4.37    inference(cnf_transformation,[],[f51])).
% 31.56/4.37  fof(f147,plain,(
% 31.56/4.37    spl4_1 | spl4_2),
% 31.56/4.37    inference(avatar_split_clause,[],[f67,f143,f139])).
% 31.56/4.37  fof(f139,plain,(
% 31.56/4.37    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 31.56/4.37    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 31.56/4.37  fof(f67,plain,(
% 31.56/4.37    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 31.56/4.37    inference(cnf_transformation,[],[f51])).
% 31.56/4.37  fof(f146,plain,(
% 31.56/4.37    ~spl4_1 | ~spl4_2),
% 31.56/4.37    inference(avatar_split_clause,[],[f68,f143,f139])).
% 31.56/4.37  fof(f68,plain,(
% 31.56/4.37    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 31.56/4.37    inference(cnf_transformation,[],[f51])).
% 31.56/4.37  % SZS output end Proof for theBenchmark
% 31.56/4.37  % (12262)------------------------------
% 31.56/4.37  % (12262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.56/4.37  % (12262)Termination reason: Refutation
% 31.56/4.37  
% 31.56/4.37  % (12262)Memory used [KB]: 31598
% 31.56/4.37  % (12262)Time elapsed: 3.913 s
% 31.56/4.37  % (12262)------------------------------
% 31.56/4.37  % (12262)------------------------------
% 31.56/4.37  % (12232)Success in time 4.02 s
%------------------------------------------------------------------------------
