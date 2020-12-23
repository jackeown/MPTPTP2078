%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 449 expanded)
%              Number of leaves         :   41 ( 179 expanded)
%              Depth                    :   19
%              Number of atoms          :  816 (1825 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3731,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f131,f136,f140,f144,f148,f152,f209,f231,f245,f344,f358,f375,f812,f1017,f1025,f1058,f1072,f1083,f1138,f1140,f1409,f1766,f3665,f3728,f3729,f3730])).

fof(f3730,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ r2_hidden(sK2,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3729,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3728,plain,
    ( spl10_31
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99
    | ~ spl10_473 ),
    inference(avatar_split_clause,[],[f3693,f3663,f762,f146,f119,f265])).

fof(f265,plain,
    ( spl10_31
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f119,plain,
    ( spl10_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f146,plain,
    ( spl10_16
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f762,plain,
    ( spl10_99
  <=> ! [X7,X8] :
        ( r1_tarski(sK1,X7)
        | ~ m1_connsp_2(sK3(sK5(sK1,X7)),sK0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,k1_tops_1(sK0,sK3(sK5(sK1,X7)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f3663,plain,
    ( spl10_473
  <=> ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).

fof(f3693,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99
    | ~ spl10_473 ),
    inference(duplicate_literal_removal,[],[f3690])).

fof(f3690,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99
    | ~ spl10_473 ),
    inference(resolution,[],[f3681,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f3681,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99
    | ~ spl10_473 ),
    inference(duplicate_literal_removal,[],[f3676])).

fof(f3676,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99
    | ~ spl10_473 ),
    inference(resolution,[],[f3664,f3462])).

fof(f3462,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X12))),X13)
        | r2_hidden(sK5(sK1,X12),X13)
        | r1_tarski(sK1,X12) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99 ),
    inference(resolution,[],[f3453,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3453,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99 ),
    inference(duplicate_literal_removal,[],[f3452])).

fof(f3452,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99 ),
    inference(resolution,[],[f3327,f211])).

fof(f211,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10 ),
    inference(resolution,[],[f191,f121])).

fof(f121,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK5(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f3327,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0)
        | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0)))) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99 ),
    inference(duplicate_literal_removal,[],[f3326])).

fof(f3326,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_99 ),
    inference(resolution,[],[f763,f1284])).

fof(f1284,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK5(sK1,X0)),sK0,sK5(sK1,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(duplicate_literal_removal,[],[f1283])).

fof(f1283,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK5(sK1,X0)),sK0,sK5(sK1,X0))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(resolution,[],[f222,f64])).

fof(f222,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK1,X1),sK1)
        | m1_connsp_2(sK3(sK5(sK1,X1)),sK0,sK5(sK1,X1))
        | r1_tarski(sK1,X1) )
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(resolution,[],[f211,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f763,plain,
    ( ! [X8,X7] :
        ( ~ m1_connsp_2(sK3(sK5(sK1,X7)),sK0,X8)
        | r1_tarski(sK1,X7)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,k1_tops_1(sK0,sK3(sK5(sK1,X7)))) )
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f762])).

fof(f3664,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_473 ),
    inference(avatar_component_clause,[],[f3663])).

fof(f3665,plain,
    ( ~ spl10_10
    | spl10_473
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_97 ),
    inference(avatar_split_clause,[],[f3661,f754,f142,f119,f3663,f119])).

fof(f142,plain,
    ( spl10_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f754,plain,
    ( spl10_97
  <=> ! [X3,X4] :
        ( r1_tarski(sK1,X3)
        | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X3))),k1_tops_1(sK0,X4))
        | ~ r1_tarski(sK3(sK5(sK1,X3)),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f3661,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_97 ),
    inference(duplicate_literal_removal,[],[f3657])).

fof(f3657,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_97 ),
    inference(resolution,[],[f755,f695])).

fof(f695,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK5(sK1,X0)),sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_15 ),
    inference(duplicate_literal_removal,[],[f694])).

fof(f694,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK5(sK1,X0)),sK1)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_15 ),
    inference(resolution,[],[f223,f64])).

fof(f223,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK1,X2),sK1)
        | r1_tarski(sK3(sK5(sK1,X2)),sK1)
        | r1_tarski(sK1,X2) )
    | ~ spl10_10
    | ~ spl10_15 ),
    inference(resolution,[],[f211,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f755,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK3(sK5(sK1,X3)),X4)
        | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X3))),k1_tops_1(sK0,X4))
        | r1_tarski(sK1,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_97 ),
    inference(avatar_component_clause,[],[f754])).

fof(f1766,plain,
    ( spl10_30
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f1762,f356,f342,f242,f261])).

fof(f261,plain,
    ( spl10_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f242,plain,
    ( spl10_27
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f342,plain,
    ( spl10_41
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1)
        | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f356,plain,
    ( spl10_43
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X3)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f1762,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(duplicate_literal_removal,[],[f1759])).

fof(f1759,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(resolution,[],[f1755,f65])).

fof(f1755,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tops_1(sK0,sK1),X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(duplicate_literal_removal,[],[f1754])).

fof(f1754,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tops_1(sK0,sK1),X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(resolution,[],[f922,f279])).

fof(f279,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_27 ),
    inference(resolution,[],[f244,f191])).

fof(f244,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f242])).

fof(f922,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK5(k1_tops_1(sK0,sK1),X5),u1_struct_0(sK0))
        | r2_hidden(sK5(k1_tops_1(sK0,sK1),X5),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X5) )
    | ~ spl10_27
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(resolution,[],[f916,f343])).

fof(f343,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(sK1,sK0,X3)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f342])).

fof(f916,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_27
    | ~ spl10_43 ),
    inference(duplicate_literal_removal,[],[f915])).

fof(f915,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_27
    | ~ spl10_43 ),
    inference(resolution,[],[f631,f279])).

fof(f631,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl10_43 ),
    inference(resolution,[],[f357,f64])).

fof(f357,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f356])).

fof(f1409,plain,
    ( spl10_31
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(avatar_split_clause,[],[f1408,f810,f373,f119,f265])).

fof(f373,plain,
    ( spl10_45
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK1,sK0,X3)
        | r2_hidden(X3,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f810,plain,
    ( spl10_111
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X4)
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f1408,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(duplicate_literal_removal,[],[f1405])).

fof(f1405,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(resolution,[],[f1402,f65])).

fof(f1402,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(duplicate_literal_removal,[],[f1401])).

fof(f1401,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(resolution,[],[f1202,f211])).

fof(f1202,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK5(sK1,X4),u1_struct_0(sK0))
        | r1_tarski(sK1,X4)
        | r2_hidden(sK5(sK1,X4),k1_tops_1(sK0,sK1)) )
    | ~ spl10_10
    | ~ spl10_45
    | ~ spl10_111 ),
    inference(resolution,[],[f1197,f374])).

fof(f374,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(sK1,sK0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,k1_tops_1(sK0,sK1)) )
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1197,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK5(sK1,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_111 ),
    inference(duplicate_literal_removal,[],[f1196])).

fof(f1196,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK5(sK1,X0))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_111 ),
    inference(resolution,[],[f1060,f64])).

fof(f1060,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0),sK1)
        | m1_connsp_2(sK1,sK0,sK5(sK1,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_111 ),
    inference(resolution,[],[f811,f211])).

fof(f811,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X4)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl10_111 ),
    inference(avatar_component_clause,[],[f810])).

fof(f1140,plain,
    ( spl10_9
    | ~ spl10_7
    | ~ spl10_8
    | spl10_99
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f1123,f150,f119,f762,f109,f104,f114])).

fof(f114,plain,
    ( spl10_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f104,plain,
    ( spl10_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f109,plain,
    ( spl10_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f150,plain,
    ( spl10_17
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f1123,plain,
    ( ! [X12,X13] :
        ( r1_tarski(sK1,X12)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X13,k1_tops_1(sK0,sK3(sK5(sK1,X12))))
        | ~ m1_connsp_2(sK3(sK5(sK1,X12)),sK0,X13) )
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(resolution,[],[f732,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f732,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(resolution,[],[f221,f64])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0),sK1)
        | m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(resolution,[],[f211,f151])).

fof(f151,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1138,plain,
    ( ~ spl10_7
    | spl10_97
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f1121,f150,f119,f754,f104])).

fof(f1121,plain,
    ( ! [X8,X9] :
        ( r1_tarski(sK1,X8)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3(sK5(sK1,X8)),X9)
        | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X8))),k1_tops_1(sK0,X9)) )
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(resolution,[],[f732,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1083,plain,
    ( ~ spl10_139
    | ~ spl10_30
    | ~ spl10_25
    | ~ spl10_27
    | ~ spl10_120 ),
    inference(avatar_split_clause,[],[f1075,f873,f242,f228,f261,f1080])).

fof(f1080,plain,
    ( spl10_139
  <=> r2_hidden(sK2,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).

fof(f228,plain,
    ( spl10_25
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f873,plain,
    ( spl10_120
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f1075,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r2_hidden(sK2,k1_tops_1(sK0,sK1))
    | ~ spl10_27
    | ~ spl10_120 ),
    inference(resolution,[],[f874,f244])).

fof(f874,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1)
        | ~ r2_hidden(sK2,X3) )
    | ~ spl10_120 ),
    inference(avatar_component_clause,[],[f873])).

fof(f1072,plain,
    ( spl10_120
    | spl10_23
    | ~ spl10_10
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f1067,f624,f119,f202,f873])).

fof(f202,plain,
    ( spl10_23
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f624,plain,
    ( spl10_88
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X0,sK0,sK2)
        | ~ r2_hidden(sK2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f1067,plain,
    ( ! [X3] :
        ( m1_connsp_2(sK1,sK0,sK2)
        | ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl10_10
    | ~ spl10_88 ),
    inference(resolution,[],[f625,f121])).

fof(f625,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X0,sK0,sK2)
        | ~ r2_hidden(sK2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f624])).

fof(f1058,plain,
    ( ~ spl10_31
    | ~ spl10_30
    | spl10_29 ),
    inference(avatar_split_clause,[],[f1056,f254,f261,f265])).

fof(f254,plain,
    ( spl10_29
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1056,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_29 ),
    inference(extensionality_resolution,[],[f62,f256])).

fof(f256,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl10_29 ),
    inference(avatar_component_clause,[],[f254])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1025,plain,
    ( spl10_88
    | spl10_9
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f1022,f133,f109,f104,f114,f624])).

fof(f133,plain,
    ( spl10_13
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1022,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ r2_hidden(sK2,X1)
        | m1_connsp_2(X0,sK0,sK2) )
    | ~ spl10_13 ),
    inference(resolution,[],[f135,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f135,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1017,plain,(
    spl10_24 ),
    inference(avatar_contradiction_clause,[],[f1016])).

fof(f1016,plain,
    ( $false
    | spl10_24 ),
    inference(resolution,[],[f208,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f208,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl10_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_24
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f812,plain,
    ( ~ spl10_11
    | spl10_111
    | spl10_9
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f502,f119,f109,f104,f114,f810,f124])).

fof(f124,plain,
    ( spl10_11
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f502,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r2_hidden(X4,sK1)
        | m1_connsp_2(sK1,sK0,X4) )
    | ~ spl10_10 ),
    inference(resolution,[],[f55,f121])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f375,plain,
    ( spl10_9
    | spl10_45
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f368,f119,f109,f104,f373,f114])).

fof(f368,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X3,k1_tops_1(sK0,sK1))
        | ~ m1_connsp_2(sK1,sK0,X3) )
    | ~ spl10_10 ),
    inference(resolution,[],[f48,f121])).

fof(f358,plain,
    ( spl10_9
    | spl10_43
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f348,f119,f109,f104,f356,f114])).

fof(f348,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X3) )
    | ~ spl10_10 ),
    inference(resolution,[],[f47,f121])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f344,plain,
    ( spl10_41
    | spl10_9
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f335,f119,f109,f104,f114,f342])).

fof(f335,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK1,sK0,X3)
        | r2_hidden(X3,sK1) )
    | ~ spl10_10 ),
    inference(resolution,[],[f54,f121])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f245,plain,
    ( spl10_27
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f239,f119,f104,f242])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_10 ),
    inference(resolution,[],[f59,f121])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f231,plain,
    ( spl10_25
    | ~ spl10_8
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f225,f119,f104,f109,f228])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl10_10 ),
    inference(resolution,[],[f58,f121])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f209,plain,
    ( ~ spl10_23
    | ~ spl10_24
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f199,f138,f119,f206,f202])).

fof(f138,plain,
    ( spl10_14
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f199,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl10_10
    | ~ spl10_14 ),
    inference(resolution,[],[f139,f121])).

fof(f139,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f152,plain,
    ( spl10_11
    | spl10_17 ),
    inference(avatar_split_clause,[],[f36,f150,f124])).

fof(f36,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f148,plain,
    ( spl10_11
    | spl10_16 ),
    inference(avatar_split_clause,[],[f37,f146,f124])).

fof(f37,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f144,plain,
    ( spl10_11
    | spl10_15 ),
    inference(avatar_split_clause,[],[f38,f142,f124])).

fof(f38,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,
    ( ~ spl10_11
    | spl10_14 ),
    inference(avatar_split_clause,[],[f39,f138,f124])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,
    ( ~ spl10_11
    | spl10_13 ),
    inference(avatar_split_clause,[],[f40,f133,f124])).

fof(f40,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f41,f128,f124])).

fof(f128,plain,
    ( spl10_12
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f41,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f122,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f42,f119])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f43,f114])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f44,f109])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:28:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (18638)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.49  % (18633)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.49  % (18652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (18644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (18659)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (18636)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (18656)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.50  % (18643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (18651)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (18648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (18632)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (18635)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (18631)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (18647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (18658)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (18641)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (18655)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (18650)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (18653)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (18634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (18656)Refutation not found, incomplete strategy% (18656)------------------------------
% 0.19/0.52  % (18656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (18646)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (18637)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (18657)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (18630)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.53  % (18640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.54  % (18649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.54  % (18639)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.54  % (18656)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.54  
% 1.48/0.54  % (18656)Memory used [KB]: 10746
% 1.48/0.54  % (18656)Time elapsed: 0.117 s
% 1.48/0.54  % (18656)------------------------------
% 1.48/0.54  % (18656)------------------------------
% 1.48/0.54  % (18654)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.54  % (18642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.54  % (18645)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.20/0.67  % (18661)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.03/0.75  % (18646)Refutation found. Thanks to Tanya!
% 3.03/0.75  % SZS status Theorem for theBenchmark
% 3.03/0.75  % SZS output start Proof for theBenchmark
% 3.03/0.75  fof(f3731,plain,(
% 3.03/0.75    $false),
% 3.03/0.75    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f131,f136,f140,f144,f148,f152,f209,f231,f245,f344,f358,f375,f812,f1017,f1025,f1058,f1072,f1083,f1138,f1140,f1409,f1766,f3665,f3728,f3729,f3730])).
% 3.03/0.75  fof(f3730,plain,(
% 3.03/0.75    sK1 != k1_tops_1(sK0,sK1) | r2_hidden(sK2,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK2,sK1)),
% 3.03/0.75    introduced(theory_tautology_sat_conflict,[])).
% 3.03/0.75  fof(f3729,plain,(
% 3.03/0.75    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.03/0.75    introduced(theory_tautology_sat_conflict,[])).
% 3.03/0.75  fof(f3728,plain,(
% 3.03/0.75    spl10_31 | ~spl10_10 | ~spl10_16 | ~spl10_99 | ~spl10_473),
% 3.03/0.75    inference(avatar_split_clause,[],[f3693,f3663,f762,f146,f119,f265])).
% 3.03/0.75  fof(f265,plain,(
% 3.03/0.75    spl10_31 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.03/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 3.03/0.75  fof(f119,plain,(
% 3.03/0.75    spl10_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.03/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 3.03/0.75  fof(f146,plain,(
% 3.03/0.75    spl10_16 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 3.03/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 3.03/0.75  fof(f762,plain,(
% 3.03/0.75    spl10_99 <=> ! [X7,X8] : (r1_tarski(sK1,X7) | ~m1_connsp_2(sK3(sK5(sK1,X7)),sK0,X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r2_hidden(X8,k1_tops_1(sK0,sK3(sK5(sK1,X7)))))),
% 3.03/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).
% 3.03/0.75  fof(f3663,plain,(
% 3.03/0.75    spl10_473 <=> ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0))),
% 3.03/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).
% 3.03/0.75  fof(f3693,plain,(
% 3.03/0.75    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl10_10 | ~spl10_16 | ~spl10_99 | ~spl10_473)),
% 3.03/0.75    inference(duplicate_literal_removal,[],[f3690])).
% 3.03/0.75  fof(f3690,plain,(
% 3.03/0.75    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl10_10 | ~spl10_16 | ~spl10_99 | ~spl10_473)),
% 3.03/0.75    inference(resolution,[],[f3681,f65])).
% 3.03/0.75  fof(f65,plain,(
% 3.03/0.75    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.03/0.75    inference(cnf_transformation,[],[f33])).
% 3.03/0.75  fof(f33,plain,(
% 3.03/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.03/0.75    inference(ennf_transformation,[],[f1])).
% 3.20/0.77  fof(f1,axiom,(
% 3.20/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.20/0.77  fof(f3681,plain,(
% 3.20/0.77    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99 | ~spl10_473)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f3676])).
% 3.20/0.77  fof(f3676,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99 | ~spl10_473)),
% 3.20/0.77    inference(resolution,[],[f3664,f3462])).
% 3.20/0.77  fof(f3462,plain,(
% 3.20/0.77    ( ! [X12,X13] : (~r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X12))),X13) | r2_hidden(sK5(sK1,X12),X13) | r1_tarski(sK1,X12)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99)),
% 3.20/0.77    inference(resolution,[],[f3453,f63])).
% 3.20/0.77  fof(f63,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f33])).
% 3.20/0.77  fof(f3453,plain,(
% 3.20/0.77    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f3452])).
% 3.20/0.77  fof(f3452,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99)),
% 3.20/0.77    inference(resolution,[],[f3327,f211])).
% 3.20/0.77  fof(f211,plain,(
% 3.20/0.77    ( ! [X0] : (m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)) ) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f191,f121])).
% 3.20/0.77  fof(f121,plain,(
% 3.20/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl10_10),
% 3.20/0.77    inference(avatar_component_clause,[],[f119])).
% 3.20/0.77  fof(f191,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK5(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 3.20/0.77    inference(resolution,[],[f68,f64])).
% 3.20/0.77  fof(f64,plain,(
% 3.20/0.77    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f33])).
% 3.20/0.77  fof(f68,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f35])).
% 3.20/0.77  fof(f35,plain,(
% 3.20/0.77    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.20/0.77    inference(flattening,[],[f34])).
% 3.20/0.77  fof(f34,plain,(
% 3.20/0.77    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.20/0.77    inference(ennf_transformation,[],[f4])).
% 3.20/0.77  fof(f4,axiom,(
% 3.20/0.77    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.20/0.77  fof(f3327,plain,(
% 3.20/0.77    ( ! [X0] : (~m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0))))) ) | (~spl10_10 | ~spl10_16 | ~spl10_99)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f3326])).
% 3.20/0.77  fof(f3326,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(sK5(sK1,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK3(sK5(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16 | ~spl10_99)),
% 3.20/0.77    inference(resolution,[],[f763,f1284])).
% 3.20/0.77  fof(f1284,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK3(sK5(sK1,X0)),sK0,sK5(sK1,X0)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1283])).
% 3.20/0.77  fof(f1283,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK3(sK5(sK1,X0)),sK0,sK5(sK1,X0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_16)),
% 3.20/0.77    inference(resolution,[],[f222,f64])).
% 3.20/0.77  fof(f222,plain,(
% 3.20/0.77    ( ! [X1] : (~r2_hidden(sK5(sK1,X1),sK1) | m1_connsp_2(sK3(sK5(sK1,X1)),sK0,sK5(sK1,X1)) | r1_tarski(sK1,X1)) ) | (~spl10_10 | ~spl10_16)),
% 3.20/0.77    inference(resolution,[],[f211,f147])).
% 3.20/0.77  fof(f147,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1)) ) | ~spl10_16),
% 3.20/0.77    inference(avatar_component_clause,[],[f146])).
% 3.20/0.77  fof(f763,plain,(
% 3.20/0.77    ( ! [X8,X7] : (~m1_connsp_2(sK3(sK5(sK1,X7)),sK0,X8) | r1_tarski(sK1,X7) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r2_hidden(X8,k1_tops_1(sK0,sK3(sK5(sK1,X7))))) ) | ~spl10_99),
% 3.20/0.77    inference(avatar_component_clause,[],[f762])).
% 3.20/0.77  fof(f3664,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | ~spl10_473),
% 3.20/0.77    inference(avatar_component_clause,[],[f3663])).
% 3.20/0.77  fof(f3665,plain,(
% 3.20/0.77    ~spl10_10 | spl10_473 | ~spl10_10 | ~spl10_15 | ~spl10_97),
% 3.20/0.77    inference(avatar_split_clause,[],[f3661,f754,f142,f119,f3663,f119])).
% 3.20/0.77  fof(f142,plain,(
% 3.20/0.77    spl10_15 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 3.20/0.77  fof(f754,plain,(
% 3.20/0.77    spl10_97 <=> ! [X3,X4] : (r1_tarski(sK1,X3) | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X3))),k1_tops_1(sK0,X4)) | ~r1_tarski(sK3(sK5(sK1,X3)),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).
% 3.20/0.77  fof(f3661,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_10 | ~spl10_15 | ~spl10_97)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f3657])).
% 3.20/0.77  fof(f3657,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_15 | ~spl10_97)),
% 3.20/0.77    inference(resolution,[],[f755,f695])).
% 3.20/0.77  fof(f695,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK3(sK5(sK1,X0)),sK1) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_15)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f694])).
% 3.20/0.77  fof(f694,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK3(sK5(sK1,X0)),sK1) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_15)),
% 3.20/0.77    inference(resolution,[],[f223,f64])).
% 3.20/0.77  fof(f223,plain,(
% 3.20/0.77    ( ! [X2] : (~r2_hidden(sK5(sK1,X2),sK1) | r1_tarski(sK3(sK5(sK1,X2)),sK1) | r1_tarski(sK1,X2)) ) | (~spl10_10 | ~spl10_15)),
% 3.20/0.77    inference(resolution,[],[f211,f143])).
% 3.20/0.77  fof(f143,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl10_15),
% 3.20/0.77    inference(avatar_component_clause,[],[f142])).
% 3.20/0.77  fof(f755,plain,(
% 3.20/0.77    ( ! [X4,X3] : (~r1_tarski(sK3(sK5(sK1,X3)),X4) | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X3))),k1_tops_1(sK0,X4)) | r1_tarski(sK1,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl10_97),
% 3.20/0.77    inference(avatar_component_clause,[],[f754])).
% 3.20/0.77  fof(f1766,plain,(
% 3.20/0.77    spl10_30 | ~spl10_27 | ~spl10_41 | ~spl10_43),
% 3.20/0.77    inference(avatar_split_clause,[],[f1762,f356,f342,f242,f261])).
% 3.20/0.77  fof(f261,plain,(
% 3.20/0.77    spl10_30 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 3.20/0.77  fof(f242,plain,(
% 3.20/0.77    spl10_27 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 3.20/0.77  fof(f342,plain,(
% 3.20/0.77    spl10_41 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1) | ~m1_connsp_2(sK1,sK0,X3))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 3.20/0.77  fof(f356,plain,(
% 3.20/0.77    spl10_43 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X3) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 3.20/0.77  fof(f1762,plain,(
% 3.20/0.77    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl10_27 | ~spl10_41 | ~spl10_43)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1759])).
% 3.20/0.77  fof(f1759,plain,(
% 3.20/0.77    r1_tarski(k1_tops_1(sK0,sK1),sK1) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl10_27 | ~spl10_41 | ~spl10_43)),
% 3.20/0.77    inference(resolution,[],[f1755,f65])).
% 3.20/0.77  fof(f1755,plain,(
% 3.20/0.77    ( ! [X0] : (r2_hidden(sK5(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl10_27 | ~spl10_41 | ~spl10_43)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1754])).
% 3.20/0.77  fof(f1754,plain,(
% 3.20/0.77    ( ! [X0] : (r2_hidden(sK5(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl10_27 | ~spl10_41 | ~spl10_43)),
% 3.20/0.77    inference(resolution,[],[f922,f279])).
% 3.20/0.77  fof(f279,plain,(
% 3.20/0.77    ( ! [X0] : (m1_subset_1(sK5(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl10_27),
% 3.20/0.77    inference(resolution,[],[f244,f191])).
% 3.20/0.77  fof(f244,plain,(
% 3.20/0.77    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl10_27),
% 3.20/0.77    inference(avatar_component_clause,[],[f242])).
% 3.20/0.77  fof(f922,plain,(
% 3.20/0.77    ( ! [X5] : (~m1_subset_1(sK5(k1_tops_1(sK0,sK1),X5),u1_struct_0(sK0)) | r2_hidden(sK5(k1_tops_1(sK0,sK1),X5),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X5)) ) | (~spl10_27 | ~spl10_41 | ~spl10_43)),
% 3.20/0.77    inference(resolution,[],[f916,f343])).
% 3.20/0.77  fof(f343,plain,(
% 3.20/0.77    ( ! [X3] : (~m1_connsp_2(sK1,sK0,X3) | r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl10_41),
% 3.20/0.77    inference(avatar_component_clause,[],[f342])).
% 3.20/0.77  fof(f916,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl10_27 | ~spl10_43)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f915])).
% 3.20/0.77  fof(f915,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl10_27 | ~spl10_43)),
% 3.20/0.77    inference(resolution,[],[f631,f279])).
% 3.20/0.77  fof(f631,plain,(
% 3.20/0.77    ( ! [X0] : (~m1_subset_1(sK5(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,sK5(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl10_43),
% 3.20/0.77    inference(resolution,[],[f357,f64])).
% 3.20/0.77  fof(f357,plain,(
% 3.20/0.77    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl10_43),
% 3.20/0.77    inference(avatar_component_clause,[],[f356])).
% 3.20/0.77  fof(f1409,plain,(
% 3.20/0.77    spl10_31 | ~spl10_10 | ~spl10_45 | ~spl10_111),
% 3.20/0.77    inference(avatar_split_clause,[],[f1408,f810,f373,f119,f265])).
% 3.20/0.77  fof(f373,plain,(
% 3.20/0.77    spl10_45 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_connsp_2(sK1,sK0,X3) | r2_hidden(X3,k1_tops_1(sK0,sK1)))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 3.20/0.77  fof(f810,plain,(
% 3.20/0.77    spl10_111 <=> ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X4) | ~r2_hidden(X4,sK1))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).
% 3.20/0.77  fof(f1408,plain,(
% 3.20/0.77    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl10_10 | ~spl10_45 | ~spl10_111)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1405])).
% 3.20/0.77  fof(f1405,plain,(
% 3.20/0.77    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl10_10 | ~spl10_45 | ~spl10_111)),
% 3.20/0.77    inference(resolution,[],[f1402,f65])).
% 3.20/0.77  fof(f1402,plain,(
% 3.20/0.77    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_45 | ~spl10_111)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1401])).
% 3.20/0.77  fof(f1401,plain,(
% 3.20/0.77    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_45 | ~spl10_111)),
% 3.20/0.77    inference(resolution,[],[f1202,f211])).
% 3.20/0.77  fof(f1202,plain,(
% 3.20/0.77    ( ! [X4] : (~m1_subset_1(sK5(sK1,X4),u1_struct_0(sK0)) | r1_tarski(sK1,X4) | r2_hidden(sK5(sK1,X4),k1_tops_1(sK0,sK1))) ) | (~spl10_10 | ~spl10_45 | ~spl10_111)),
% 3.20/0.77    inference(resolution,[],[f1197,f374])).
% 3.20/0.77  fof(f374,plain,(
% 3.20/0.77    ( ! [X3] : (~m1_connsp_2(sK1,sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k1_tops_1(sK0,sK1))) ) | ~spl10_45),
% 3.20/0.77    inference(avatar_component_clause,[],[f373])).
% 3.20/0.77  fof(f1197,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK5(sK1,X0)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_111)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f1196])).
% 3.20/0.77  fof(f1196,plain,(
% 3.20/0.77    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK5(sK1,X0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_111)),
% 3.20/0.77    inference(resolution,[],[f1060,f64])).
% 3.20/0.77  fof(f1060,plain,(
% 3.20/0.77    ( ! [X0] : (~r2_hidden(sK5(sK1,X0),sK1) | m1_connsp_2(sK1,sK0,sK5(sK1,X0)) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_111)),
% 3.20/0.77    inference(resolution,[],[f811,f211])).
% 3.20/0.77  fof(f811,plain,(
% 3.20/0.77    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X4) | ~r2_hidden(X4,sK1)) ) | ~spl10_111),
% 3.20/0.77    inference(avatar_component_clause,[],[f810])).
% 3.20/0.77  fof(f1140,plain,(
% 3.20/0.77    spl10_9 | ~spl10_7 | ~spl10_8 | spl10_99 | ~spl10_10 | ~spl10_17),
% 3.20/0.77    inference(avatar_split_clause,[],[f1123,f150,f119,f762,f109,f104,f114])).
% 3.20/0.77  fof(f114,plain,(
% 3.20/0.77    spl10_9 <=> v2_struct_0(sK0)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 3.20/0.77  fof(f104,plain,(
% 3.20/0.77    spl10_7 <=> l1_pre_topc(sK0)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 3.20/0.77  fof(f109,plain,(
% 3.20/0.77    spl10_8 <=> v2_pre_topc(sK0)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 3.20/0.77  fof(f150,plain,(
% 3.20/0.77    spl10_17 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 3.20/0.77  fof(f1123,plain,(
% 3.20/0.77    ( ! [X12,X13] : (r1_tarski(sK1,X12) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X13,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X13,k1_tops_1(sK0,sK3(sK5(sK1,X12)))) | ~m1_connsp_2(sK3(sK5(sK1,X12)),sK0,X13)) ) | (~spl10_10 | ~spl10_17)),
% 3.20/0.77    inference(resolution,[],[f732,f48])).
% 3.20/0.77  fof(f48,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f20])).
% 3.20/0.77  fof(f20,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.77    inference(flattening,[],[f19])).
% 3.20/0.77  fof(f19,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f9])).
% 3.20/0.77  fof(f9,axiom,(
% 3.20/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 3.20/0.77  fof(f732,plain,(
% 3.20/0.77    ( ! [X0] : (m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_17)),
% 3.20/0.77    inference(duplicate_literal_removal,[],[f731])).
% 3.20/0.77  fof(f731,plain,(
% 3.20/0.77    ( ! [X0] : (m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_17)),
% 3.20/0.77    inference(resolution,[],[f221,f64])).
% 3.20/0.77  fof(f221,plain,(
% 3.20/0.77    ( ! [X0] : (~r2_hidden(sK5(sK1,X0),sK1) | m1_subset_1(sK3(sK5(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl10_10 | ~spl10_17)),
% 3.20/0.77    inference(resolution,[],[f211,f151])).
% 3.20/0.77  fof(f151,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1)) ) | ~spl10_17),
% 3.20/0.77    inference(avatar_component_clause,[],[f150])).
% 3.20/0.77  fof(f1138,plain,(
% 3.20/0.77    ~spl10_7 | spl10_97 | ~spl10_10 | ~spl10_17),
% 3.20/0.77    inference(avatar_split_clause,[],[f1121,f150,f119,f754,f104])).
% 3.20/0.77  fof(f1121,plain,(
% 3.20/0.77    ( ! [X8,X9] : (r1_tarski(sK1,X8) | ~l1_pre_topc(sK0) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3(sK5(sK1,X8)),X9) | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,X8))),k1_tops_1(sK0,X9))) ) | (~spl10_10 | ~spl10_17)),
% 3.20/0.77    inference(resolution,[],[f732,f46])).
% 3.20/0.77  fof(f46,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 3.20/0.77    inference(cnf_transformation,[],[f18])).
% 3.20/0.77  fof(f18,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.77    inference(flattening,[],[f17])).
% 3.20/0.77  fof(f17,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.77    inference(ennf_transformation,[],[f7])).
% 3.20/0.77  fof(f7,axiom,(
% 3.20/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 3.20/0.77  fof(f1083,plain,(
% 3.20/0.77    ~spl10_139 | ~spl10_30 | ~spl10_25 | ~spl10_27 | ~spl10_120),
% 3.20/0.77    inference(avatar_split_clause,[],[f1075,f873,f242,f228,f261,f1080])).
% 3.20/0.77  fof(f1080,plain,(
% 3.20/0.77    spl10_139 <=> r2_hidden(sK2,k1_tops_1(sK0,sK1))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).
% 3.20/0.77  fof(f228,plain,(
% 3.20/0.77    spl10_25 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 3.20/0.77  fof(f873,plain,(
% 3.20/0.77    spl10_120 <=> ! [X3] : (~r2_hidden(sK2,X3) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).
% 3.20/0.77  fof(f1075,plain,(
% 3.20/0.77    ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~r2_hidden(sK2,k1_tops_1(sK0,sK1)) | (~spl10_27 | ~spl10_120)),
% 3.20/0.77    inference(resolution,[],[f874,f244])).
% 3.20/0.77  fof(f874,plain,(
% 3.20/0.77    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~r2_hidden(sK2,X3)) ) | ~spl10_120),
% 3.20/0.77    inference(avatar_component_clause,[],[f873])).
% 3.20/0.77  fof(f1072,plain,(
% 3.20/0.77    spl10_120 | spl10_23 | ~spl10_10 | ~spl10_88),
% 3.20/0.77    inference(avatar_split_clause,[],[f1067,f624,f119,f202,f873])).
% 3.20/0.77  fof(f202,plain,(
% 3.20/0.77    spl10_23 <=> m1_connsp_2(sK1,sK0,sK2)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 3.20/0.77  fof(f624,plain,(
% 3.20/0.77    spl10_88 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK2) | ~r2_hidden(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v3_pre_topc(X1,sK0))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).
% 3.20/0.77  fof(f1067,plain,(
% 3.20/0.77    ( ! [X3] : (m1_connsp_2(sK1,sK0,sK2) | ~r2_hidden(sK2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | (~spl10_10 | ~spl10_88)),
% 3.20/0.77    inference(resolution,[],[f625,f121])).
% 3.20/0.77  fof(f625,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK2) | ~r2_hidden(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v3_pre_topc(X1,sK0)) ) | ~spl10_88),
% 3.20/0.77    inference(avatar_component_clause,[],[f624])).
% 3.20/0.77  fof(f1058,plain,(
% 3.20/0.77    ~spl10_31 | ~spl10_30 | spl10_29),
% 3.20/0.77    inference(avatar_split_clause,[],[f1056,f254,f261,f265])).
% 3.20/0.77  fof(f254,plain,(
% 3.20/0.77    spl10_29 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 3.20/0.77  fof(f1056,plain,(
% 3.20/0.77    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_29),
% 3.20/0.77    inference(extensionality_resolution,[],[f62,f256])).
% 3.20/0.77  fof(f256,plain,(
% 3.20/0.77    sK1 != k1_tops_1(sK0,sK1) | spl10_29),
% 3.20/0.77    inference(avatar_component_clause,[],[f254])).
% 3.20/0.77  fof(f62,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.20/0.77    inference(cnf_transformation,[],[f2])).
% 3.20/0.77  fof(f2,axiom,(
% 3.20/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.20/0.77  fof(f1025,plain,(
% 3.20/0.77    spl10_88 | spl10_9 | ~spl10_7 | ~spl10_8 | ~spl10_13),
% 3.20/0.77    inference(avatar_split_clause,[],[f1022,f133,f109,f104,f114,f624])).
% 3.20/0.77  fof(f133,plain,(
% 3.20/0.77    spl10_13 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 3.20/0.77  fof(f1022,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r1_tarski(X1,X0) | ~r2_hidden(sK2,X1) | m1_connsp_2(X0,sK0,sK2)) ) | ~spl10_13),
% 3.20/0.77    inference(resolution,[],[f135,f53])).
% 3.20/0.77  fof(f53,plain,(
% 3.20/0.77    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | m1_connsp_2(X2,X0,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f22])).
% 3.20/0.77  fof(f22,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.77    inference(flattening,[],[f21])).
% 3.20/0.77  fof(f21,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f12])).
% 3.20/0.77  fof(f12,axiom,(
% 3.20/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 3.20/0.77  fof(f135,plain,(
% 3.20/0.77    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl10_13),
% 3.20/0.77    inference(avatar_component_clause,[],[f133])).
% 3.20/0.77  fof(f1017,plain,(
% 3.20/0.77    spl10_24),
% 3.20/0.77    inference(avatar_contradiction_clause,[],[f1016])).
% 3.20/0.77  fof(f1016,plain,(
% 3.20/0.77    $false | spl10_24),
% 3.20/0.77    inference(resolution,[],[f208,f69])).
% 3.20/0.77  fof(f69,plain,(
% 3.20/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/0.77    inference(equality_resolution,[],[f61])).
% 3.20/0.77  fof(f61,plain,(
% 3.20/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.20/0.77    inference(cnf_transformation,[],[f2])).
% 3.20/0.77  fof(f208,plain,(
% 3.20/0.77    ~r1_tarski(sK1,sK1) | spl10_24),
% 3.20/0.77    inference(avatar_component_clause,[],[f206])).
% 3.20/0.77  fof(f206,plain,(
% 3.20/0.77    spl10_24 <=> r1_tarski(sK1,sK1)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 3.20/0.77  fof(f812,plain,(
% 3.20/0.77    ~spl10_11 | spl10_111 | spl10_9 | ~spl10_7 | ~spl10_8 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f502,f119,f109,f104,f114,f810,f124])).
% 3.20/0.77  fof(f124,plain,(
% 3.20/0.77    spl10_11 <=> v3_pre_topc(sK1,sK0)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 3.20/0.77  fof(f502,plain,(
% 3.20/0.77    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~r2_hidden(X4,sK1) | m1_connsp_2(sK1,sK0,X4)) ) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f55,f121])).
% 3.20/0.77  fof(f55,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f26])).
% 3.20/0.77  fof(f26,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.77    inference(flattening,[],[f25])).
% 3.20/0.77  fof(f25,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f10])).
% 3.20/0.77  fof(f10,axiom,(
% 3.20/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 3.20/0.77  fof(f375,plain,(
% 3.20/0.77    spl10_9 | spl10_45 | ~spl10_7 | ~spl10_8 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f368,f119,f109,f104,f373,f114])).
% 3.20/0.77  fof(f368,plain,(
% 3.20/0.77    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,X3)) ) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f48,f121])).
% 3.20/0.77  fof(f358,plain,(
% 3.20/0.77    spl10_9 | spl10_43 | ~spl10_7 | ~spl10_8 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f348,f119,f109,f104,f356,f114])).
% 3.20/0.77  fof(f348,plain,(
% 3.20/0.77    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X3)) ) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f47,f121])).
% 3.20/0.77  fof(f47,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f20])).
% 3.20/0.77  fof(f344,plain,(
% 3.20/0.77    spl10_41 | spl10_9 | ~spl10_7 | ~spl10_8 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f335,f119,f109,f104,f114,f342])).
% 3.20/0.77  fof(f335,plain,(
% 3.20/0.77    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_connsp_2(sK1,sK0,X3) | r2_hidden(X3,sK1)) ) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f54,f121])).
% 3.20/0.77  fof(f54,plain,(
% 3.20/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f24])).
% 3.20/0.77  fof(f24,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.77    inference(flattening,[],[f23])).
% 3.20/0.77  fof(f23,plain,(
% 3.20/0.77    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f11])).
% 3.20/0.77  fof(f11,axiom,(
% 3.20/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 3.20/0.77  fof(f245,plain,(
% 3.20/0.77    spl10_27 | ~spl10_7 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f239,f119,f104,f242])).
% 3.20/0.77  fof(f239,plain,(
% 3.20/0.77    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f59,f121])).
% 3.20/0.77  fof(f59,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.20/0.77    inference(cnf_transformation,[],[f32])).
% 3.20/0.77  fof(f32,plain,(
% 3.20/0.77    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.20/0.77    inference(flattening,[],[f31])).
% 3.20/0.77  fof(f31,plain,(
% 3.20/0.77    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f5])).
% 3.20/0.77  fof(f5,axiom,(
% 3.20/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 3.20/0.77  fof(f231,plain,(
% 3.20/0.77    spl10_25 | ~spl10_8 | ~spl10_7 | ~spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f225,f119,f104,f109,f228])).
% 3.20/0.77  fof(f225,plain,(
% 3.20/0.77    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl10_10),
% 3.20/0.77    inference(resolution,[],[f58,f121])).
% 3.20/0.77  fof(f58,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f30])).
% 3.20/0.77  fof(f30,plain,(
% 3.20/0.77    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.20/0.77    inference(flattening,[],[f29])).
% 3.20/0.77  fof(f29,plain,(
% 3.20/0.77    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f6])).
% 3.20/0.77  fof(f6,axiom,(
% 3.20/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.20/0.77  fof(f209,plain,(
% 3.20/0.77    ~spl10_23 | ~spl10_24 | ~spl10_10 | ~spl10_14),
% 3.20/0.77    inference(avatar_split_clause,[],[f199,f138,f119,f206,f202])).
% 3.20/0.77  fof(f138,plain,(
% 3.20/0.77    spl10_14 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 3.20/0.77  fof(f199,plain,(
% 3.20/0.77    ~r1_tarski(sK1,sK1) | ~m1_connsp_2(sK1,sK0,sK2) | (~spl10_10 | ~spl10_14)),
% 3.20/0.77    inference(resolution,[],[f139,f121])).
% 3.20/0.77  fof(f139,plain,(
% 3.20/0.77    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl10_14),
% 3.20/0.77    inference(avatar_component_clause,[],[f138])).
% 3.20/0.77  fof(f152,plain,(
% 3.20/0.77    spl10_11 | spl10_17),
% 3.20/0.77    inference(avatar_split_clause,[],[f36,f150,f124])).
% 3.20/0.77  fof(f36,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f16,plain,(
% 3.20/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.77    inference(flattening,[],[f15])).
% 3.20/0.77  fof(f15,plain,(
% 3.20/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.20/0.77    inference(ennf_transformation,[],[f14])).
% 3.20/0.77  fof(f14,negated_conjecture,(
% 3.20/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.20/0.77    inference(negated_conjecture,[],[f13])).
% 3.20/0.77  fof(f13,conjecture,(
% 3.20/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.20/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 3.20/0.77  fof(f148,plain,(
% 3.20/0.77    spl10_11 | spl10_16),
% 3.20/0.77    inference(avatar_split_clause,[],[f37,f146,f124])).
% 3.20/0.77  fof(f37,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f144,plain,(
% 3.20/0.77    spl10_11 | spl10_15),
% 3.20/0.77    inference(avatar_split_clause,[],[f38,f142,f124])).
% 3.20/0.77  fof(f38,plain,(
% 3.20/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f140,plain,(
% 3.20/0.77    ~spl10_11 | spl10_14),
% 3.20/0.77    inference(avatar_split_clause,[],[f39,f138,f124])).
% 3.20/0.77  fof(f39,plain,(
% 3.20/0.77    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f136,plain,(
% 3.20/0.77    ~spl10_11 | spl10_13),
% 3.20/0.77    inference(avatar_split_clause,[],[f40,f133,f124])).
% 3.20/0.77  fof(f40,plain,(
% 3.20/0.77    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f131,plain,(
% 3.20/0.77    ~spl10_11 | spl10_12),
% 3.20/0.77    inference(avatar_split_clause,[],[f41,f128,f124])).
% 3.20/0.77  fof(f128,plain,(
% 3.20/0.77    spl10_12 <=> r2_hidden(sK2,sK1)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 3.20/0.77  fof(f41,plain,(
% 3.20/0.77    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f122,plain,(
% 3.20/0.77    spl10_10),
% 3.20/0.77    inference(avatar_split_clause,[],[f42,f119])).
% 3.20/0.77  fof(f42,plain,(
% 3.20/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f117,plain,(
% 3.20/0.77    ~spl10_9),
% 3.20/0.77    inference(avatar_split_clause,[],[f43,f114])).
% 3.20/0.77  fof(f43,plain,(
% 3.20/0.77    ~v2_struct_0(sK0)),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f112,plain,(
% 3.20/0.77    spl10_8),
% 3.20/0.77    inference(avatar_split_clause,[],[f44,f109])).
% 3.20/0.77  fof(f44,plain,(
% 3.20/0.77    v2_pre_topc(sK0)),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  fof(f107,plain,(
% 3.20/0.77    spl10_7),
% 3.20/0.77    inference(avatar_split_clause,[],[f45,f104])).
% 3.20/0.77  fof(f45,plain,(
% 3.20/0.77    l1_pre_topc(sK0)),
% 3.20/0.77    inference(cnf_transformation,[],[f16])).
% 3.20/0.77  % SZS output end Proof for theBenchmark
% 3.20/0.77  % (18646)------------------------------
% 3.20/0.77  % (18646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.77  % (18646)Termination reason: Refutation
% 3.20/0.77  
% 3.20/0.77  % (18646)Memory used [KB]: 13560
% 3.20/0.77  % (18646)Time elapsed: 0.365 s
% 3.20/0.77  % (18646)------------------------------
% 3.20/0.77  % (18646)------------------------------
% 3.20/0.77  % (18629)Success in time 0.426 s
%------------------------------------------------------------------------------
