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
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 438 expanded)
%              Number of leaves         :   47 ( 186 expanded)
%              Depth                    :   19
%              Number of atoms          :  809 (1760 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5029,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f94,f98,f103,f108,f113,f118,f127,f132,f136,f140,f144,f148,f164,f219,f233,f264,f323,f338,f1048,f1062,f1319,f1437,f1442,f1512,f1784,f1786,f2370,f4140,f4158,f4182,f5027,f5028])).

fof(f5028,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ m1_connsp_2(sK1,sK0,sK2)
    | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5027,plain,
    ( ~ spl9_12
    | spl9_23
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f5018,f1046,f129,f195,f124])).

fof(f124,plain,
    ( spl9_12
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f195,plain,
    ( spl9_23
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f129,plain,
    ( spl9_13
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1046,plain,
    ( spl9_156
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X4)
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f5018,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(resolution,[],[f1047,f131])).

fof(f131,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1047,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X4)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f4182,plain,
    ( spl9_33
    | ~ spl9_34
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f2375,f230,f268,f261])).

fof(f261,plain,
    ( spl9_33
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f268,plain,
    ( spl9_34
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f230,plain,
    ( spl9_27
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f2375,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl9_27 ),
    inference(resolution,[],[f231,f57])).

fof(f57,plain,(
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

fof(f231,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f4158,plain,
    ( spl9_34
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149
    | ~ spl9_512 ),
    inference(avatar_split_clause,[],[f4157,f4138,f1018,f142,f115,f268])).

fof(f115,plain,
    ( spl9_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f142,plain,
    ( spl9_16
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1018,plain,
    ( spl9_149
  <=> ! [X7,X8] :
        ( r1_tarski(sK1,X7)
        | ~ m1_connsp_2(sK3(sK4(sK1,X7)),sK0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,k1_tops_1(sK0,sK3(sK4(sK1,X7)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f4138,plain,
    ( spl9_512
  <=> ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_512])])).

fof(f4157,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149
    | ~ spl9_512 ),
    inference(duplicate_literal_removal,[],[f4154])).

fof(f4154,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149
    | ~ spl9_512 ),
    inference(resolution,[],[f4152,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f4152,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149
    | ~ spl9_512 ),
    inference(duplicate_literal_removal,[],[f4145])).

fof(f4145,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149
    | ~ spl9_512 ),
    inference(resolution,[],[f4139,f4118])).

fof(f4118,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),X4)
        | r2_hidden(sK4(sK1,X3),X4)
        | r1_tarski(sK1,X3) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149 ),
    inference(resolution,[],[f4115,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4115,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149 ),
    inference(duplicate_literal_removal,[],[f4114])).

fof(f4114,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149 ),
    inference(resolution,[],[f3918,f211])).

fof(f211,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f189,f117])).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f3918,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149 ),
    inference(duplicate_literal_removal,[],[f3917])).

fof(f3917,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_149 ),
    inference(resolution,[],[f1019,f1118])).

fof(f1118,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(duplicate_literal_removal,[],[f1117])).

fof(f1117,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(resolution,[],[f325,f59])).

fof(f325,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,X1),sK1)
        | m1_connsp_2(sK3(sK4(sK1,X1)),sK0,sK4(sK1,X1))
        | r1_tarski(sK1,X1) )
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(resolution,[],[f211,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1019,plain,
    ( ! [X8,X7] :
        ( ~ m1_connsp_2(sK3(sK4(sK1,X7)),sK0,X8)
        | r1_tarski(sK1,X7)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,k1_tops_1(sK0,sK3(sK4(sK1,X7)))) )
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f4139,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl9_512 ),
    inference(avatar_component_clause,[],[f4138])).

fof(f4140,plain,
    ( ~ spl9_10
    | spl9_512
    | ~ spl9_10
    | ~ spl9_15
    | ~ spl9_147 ),
    inference(avatar_split_clause,[],[f4136,f1010,f138,f115,f4138,f115])).

fof(f138,plain,
    ( spl9_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f1010,plain,
    ( spl9_147
  <=> ! [X3,X4] :
        ( r1_tarski(sK1,X3)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),k1_tops_1(sK0,X4))
        | ~ r1_tarski(sK3(sK4(sK1,X3)),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f4136,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_10
    | ~ spl9_15
    | ~ spl9_147 ),
    inference(duplicate_literal_removal,[],[f4132])).

fof(f4132,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_15
    | ~ spl9_147 ),
    inference(resolution,[],[f1011,f976])).

fof(f976,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK4(sK1,X0)),sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f975])).

fof(f975,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK4(sK1,X0)),sK1)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(resolution,[],[f326,f59])).

fof(f326,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(sK1,X2),sK1)
        | r1_tarski(sK3(sK4(sK1,X2)),sK1)
        | r1_tarski(sK1,X2) )
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(resolution,[],[f211,f139])).

fof(f139,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1011,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK3(sK4(sK1,X3)),X4)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),k1_tops_1(sK0,X4))
        | r1_tarski(sK1,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_147 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f2370,plain,
    ( spl9_27
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f2366,f336,f321,f216,f230])).

fof(f216,plain,
    ( spl9_25
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f321,plain,
    ( spl9_40
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1)
        | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f336,plain,
    ( spl9_42
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X3)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f2366,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(duplicate_literal_removal,[],[f2363])).

fof(f2363,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(resolution,[],[f2359,f60])).

fof(f2359,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(duplicate_literal_removal,[],[f2358])).

fof(f2358,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(resolution,[],[f973,f223])).

fof(f223,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_25 ),
    inference(resolution,[],[f218,f189])).

fof(f218,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f973,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(k1_tops_1(sK0,sK1),X1),u1_struct_0(sK0))
        | r2_hidden(sK4(k1_tops_1(sK0,sK1),X1),sK1)
        | r1_tarski(k1_tops_1(sK0,sK1),X1) )
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_42 ),
    inference(resolution,[],[f703,f322])).

fof(f322,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(sK1,sK0,X3)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f321])).

fof(f703,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_25
    | ~ spl9_42 ),
    inference(duplicate_literal_removal,[],[f702])).

fof(f702,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_25
    | ~ spl9_42 ),
    inference(resolution,[],[f437,f223])).

fof(f437,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0))
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_42 ),
    inference(resolution,[],[f337,f59])).

fof(f337,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f336])).

fof(f1786,plain,
    ( spl9_9
    | ~ spl9_7
    | ~ spl9_8
    | spl9_149
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f1774,f146,f115,f1018,f105,f100,f110])).

fof(f110,plain,
    ( spl9_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f100,plain,
    ( spl9_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f105,plain,
    ( spl9_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f146,plain,
    ( spl9_17
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f1774,plain,
    ( ! [X6,X7] :
        ( r1_tarski(sK1,X6)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X7,k1_tops_1(sK0,sK3(sK4(sK1,X6))))
        | ~ m1_connsp_2(sK3(sK4(sK1,X6)),sK0,X7) )
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(resolution,[],[f993,f48])).

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

fof(f993,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(duplicate_literal_removal,[],[f992])).

fof(f992,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(resolution,[],[f324,f59])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK1)
        | m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(resolution,[],[f211,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1784,plain,
    ( ~ spl9_7
    | spl9_147
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f1772,f146,f115,f1010,f100])).

fof(f1772,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK1,X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3(sK4(sK1,X2)),X3)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3)) )
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(resolution,[],[f993,f46])).

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

fof(f1512,plain,
    ( ~ spl9_7
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f1501,f115,f80,f100])).

fof(f80,plain,
    ( spl9_2
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1501,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(resolution,[],[f81,f117])).

fof(f81,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1442,plain,
    ( ~ spl9_7
    | ~ spl9_11
    | spl9_33
    | ~ spl9_5
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f275,f115,f92,f261,f120,f100])).

fof(f120,plain,
    ( spl9_11
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f92,plain,
    ( spl9_5
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f275,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_5
    | ~ spl9_10 ),
    inference(resolution,[],[f93,f117])).

fof(f93,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1437,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1319,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | ~ spl9_6
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f1317,f161,f96,f105,f100])).

fof(f96,plain,
    ( spl9_6
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP5(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f161,plain,
    ( spl9_19
  <=> sP5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1317,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_19 ),
    inference(resolution,[],[f97,f163])).

fof(f163,plain,
    ( sP5(sK0)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ sP5(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1062,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | ~ spl9_3
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f1061,f248,f84,f105,f100])).

fof(f84,plain,
    ( spl9_3
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP7(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f248,plain,
    ( spl9_30
  <=> sP7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f1061,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_3
    | ~ spl9_30 ),
    inference(resolution,[],[f250,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ sP7(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f250,plain,
    ( sP7(sK0)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f1048,plain,
    ( ~ spl9_11
    | spl9_156
    | spl9_9
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f410,f115,f105,f100,f110,f1046,f120])).

fof(f410,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r2_hidden(X4,sK1)
        | m1_connsp_2(sK1,sK0,X4) )
    | ~ spl9_10 ),
    inference(resolution,[],[f50,f117])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f338,plain,
    ( spl9_9
    | spl9_42
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f329,f115,f105,f100,f336,f110])).

fof(f329,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X3) )
    | ~ spl9_10 ),
    inference(resolution,[],[f47,f117])).

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

fof(f323,plain,
    ( spl9_40
    | spl9_9
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f314,f115,f105,f100,f110,f321])).

fof(f314,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK1,sK0,X3)
        | r2_hidden(X3,sK1) )
    | ~ spl9_10 ),
    inference(resolution,[],[f49,f117])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f264,plain,
    ( spl9_30
    | spl9_11
    | ~ spl9_33
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f246,f115,f261,f120,f248])).

fof(f246,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | sP7(sK0)
    | ~ spl9_10 ),
    inference(resolution,[],[f71,f117])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0)
      | sP7(X0) ) ),
    inference(cnf_transformation,[],[f71_D])).

fof(f71_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | k1_tops_1(X0,X2) != X2
          | v3_pre_topc(X2,X0) )
    <=> ~ sP7(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f233,plain,
    ( ~ spl9_26
    | ~ spl9_27
    | ~ spl9_14
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f220,f216,f134,f230,f226])).

fof(f226,plain,
    ( spl9_26
  <=> m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f134,plain,
    ( spl9_14
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f220,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2)
    | ~ spl9_14
    | ~ spl9_25 ),
    inference(resolution,[],[f218,f135])).

fof(f135,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f219,plain,
    ( spl9_25
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f213,f115,f100,f216])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(resolution,[],[f54,f117])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f164,plain,
    ( spl9_19
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f158,f115,f161])).

fof(f158,plain,
    ( sP5(sK0)
    | ~ spl9_10 ),
    inference(resolution,[],[f67,f117])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f148,plain,
    ( spl9_11
    | spl9_17 ),
    inference(avatar_split_clause,[],[f36,f146,f120])).

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

fof(f144,plain,
    ( spl9_11
    | spl9_16 ),
    inference(avatar_split_clause,[],[f37,f142,f120])).

fof(f37,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,
    ( spl9_11
    | spl9_15 ),
    inference(avatar_split_clause,[],[f38,f138,f120])).

fof(f38,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,
    ( ~ spl9_11
    | spl9_14 ),
    inference(avatar_split_clause,[],[f39,f134,f120])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,
    ( ~ spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f40,f129,f120])).

fof(f40,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,
    ( ~ spl9_11
    | spl9_12 ),
    inference(avatar_split_clause,[],[f41,f124,f120])).

fof(f41,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f43,f110])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f44,f105])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,
    ( spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f69,f96,f88])).

fof(f88,plain,
    ( spl9_4
  <=> sP6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ sP5(X0)
      | sP6 ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP5(X0) )
  <=> ~ sP6 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f94,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f70,f92,f88])).

fof(f70,plain,(
    ! [X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ sP6 ) ),
    inference(general_splitting,[],[f68,f69_D])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f52,f67_D])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f86,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f73,f84,f76])).

fof(f76,plain,
    ( spl9_1
  <=> sP8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ sP7(X0)
      | sP8 ) ),
    inference(cnf_transformation,[],[f73_D])).

fof(f73_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP7(X0) )
  <=> ~ sP8 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f82,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f74,f80,f76])).

fof(f74,plain,(
    ! [X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP8 ) ),
    inference(general_splitting,[],[f72,f73_D])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP7(X0) ) ),
    inference(general_splitting,[],[f51,f71_D])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:06:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (15602)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (15607)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15615)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (15625)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (15608)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15616)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15614)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15624)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (15612)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (15606)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.56  % (15603)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.56  % (15626)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.56  % (15605)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.56  % (15609)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (15617)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.56  % (15596)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.57  % (15619)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.57  % (15601)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.57  % (15598)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.57  % (15600)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.58  % (15611)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.58  % (15621)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.58  % (15597)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.58  % (15627)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.58  % (15620)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.58  % (15628)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.58  % (15618)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.59  % (15610)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.59  % (15613)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.60  % (15622)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 3.12/0.77  % (15614)Refutation found. Thanks to Tanya!
% 3.12/0.77  % SZS status Theorem for theBenchmark
% 3.12/0.77  % SZS output start Proof for theBenchmark
% 3.12/0.80  fof(f5029,plain,(
% 3.12/0.80    $false),
% 3.12/0.80    inference(avatar_sat_refutation,[],[f82,f86,f94,f98,f103,f108,f113,f118,f127,f132,f136,f140,f144,f148,f164,f219,f233,f264,f323,f338,f1048,f1062,f1319,f1437,f1442,f1512,f1784,f1786,f2370,f4140,f4158,f4182,f5027,f5028])).
% 3.12/0.80  fof(f5028,plain,(
% 3.12/0.80    sK1 != k1_tops_1(sK0,sK1) | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,sK2) | m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2)),
% 3.12/0.80    introduced(theory_tautology_sat_conflict,[])).
% 3.12/0.80  fof(f5027,plain,(
% 3.12/0.80    ~spl9_12 | spl9_23 | ~spl9_13 | ~spl9_156),
% 3.12/0.80    inference(avatar_split_clause,[],[f5018,f1046,f129,f195,f124])).
% 3.12/0.80  fof(f124,plain,(
% 3.12/0.80    spl9_12 <=> r2_hidden(sK2,sK1)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.12/0.80  fof(f195,plain,(
% 3.12/0.80    spl9_23 <=> m1_connsp_2(sK1,sK0,sK2)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 3.12/0.80  fof(f129,plain,(
% 3.12/0.80    spl9_13 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 3.12/0.80  fof(f1046,plain,(
% 3.12/0.80    spl9_156 <=> ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X4) | ~r2_hidden(X4,sK1))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).
% 3.12/0.80  fof(f5018,plain,(
% 3.12/0.80    m1_connsp_2(sK1,sK0,sK2) | ~r2_hidden(sK2,sK1) | (~spl9_13 | ~spl9_156)),
% 3.12/0.80    inference(resolution,[],[f1047,f131])).
% 3.12/0.80  fof(f131,plain,(
% 3.12/0.80    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl9_13),
% 3.12/0.80    inference(avatar_component_clause,[],[f129])).
% 3.12/0.80  fof(f1047,plain,(
% 3.12/0.80    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X4) | ~r2_hidden(X4,sK1)) ) | ~spl9_156),
% 3.12/0.80    inference(avatar_component_clause,[],[f1046])).
% 3.12/0.80  fof(f4182,plain,(
% 3.12/0.80    spl9_33 | ~spl9_34 | ~spl9_27),
% 3.12/0.80    inference(avatar_split_clause,[],[f2375,f230,f268,f261])).
% 3.12/0.80  fof(f261,plain,(
% 3.12/0.80    spl9_33 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 3.12/0.80  fof(f268,plain,(
% 3.12/0.80    spl9_34 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 3.12/0.80  fof(f230,plain,(
% 3.12/0.80    spl9_27 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 3.12/0.80  fof(f2375,plain,(
% 3.12/0.80    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1) | ~spl9_27),
% 3.12/0.80    inference(resolution,[],[f231,f57])).
% 3.12/0.80  fof(f57,plain,(
% 3.12/0.80    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.12/0.80    inference(cnf_transformation,[],[f2])).
% 3.12/0.80  fof(f2,axiom,(
% 3.12/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.12/0.80  fof(f231,plain,(
% 3.12/0.80    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl9_27),
% 3.12/0.80    inference(avatar_component_clause,[],[f230])).
% 3.12/0.80  fof(f4158,plain,(
% 3.12/0.80    spl9_34 | ~spl9_10 | ~spl9_16 | ~spl9_149 | ~spl9_512),
% 3.12/0.80    inference(avatar_split_clause,[],[f4157,f4138,f1018,f142,f115,f268])).
% 3.12/0.80  fof(f115,plain,(
% 3.12/0.80    spl9_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 3.12/0.80  fof(f142,plain,(
% 3.12/0.80    spl9_16 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 3.12/0.80  fof(f1018,plain,(
% 3.12/0.80    spl9_149 <=> ! [X7,X8] : (r1_tarski(sK1,X7) | ~m1_connsp_2(sK3(sK4(sK1,X7)),sK0,X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r2_hidden(X8,k1_tops_1(sK0,sK3(sK4(sK1,X7)))))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).
% 3.12/0.80  fof(f4138,plain,(
% 3.12/0.80    spl9_512 <=> ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_512])])).
% 3.12/0.80  fof(f4157,plain,(
% 3.12/0.80    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl9_10 | ~spl9_16 | ~spl9_149 | ~spl9_512)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f4154])).
% 3.12/0.80  fof(f4154,plain,(
% 3.12/0.80    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl9_10 | ~spl9_16 | ~spl9_149 | ~spl9_512)),
% 3.12/0.80    inference(resolution,[],[f4152,f60])).
% 3.12/0.80  fof(f60,plain,(
% 3.12/0.80    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f31])).
% 3.12/0.80  fof(f31,plain,(
% 3.12/0.80    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f1])).
% 3.12/0.80  fof(f1,axiom,(
% 3.12/0.80    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.12/0.80  fof(f4152,plain,(
% 3.12/0.80    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149 | ~spl9_512)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f4145])).
% 3.12/0.80  fof(f4145,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149 | ~spl9_512)),
% 3.12/0.80    inference(resolution,[],[f4139,f4118])).
% 3.12/0.80  fof(f4118,plain,(
% 3.12/0.80    ( ! [X4,X3] : (~r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),X4) | r2_hidden(sK4(sK1,X3),X4) | r1_tarski(sK1,X3)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149)),
% 3.12/0.80    inference(resolution,[],[f4115,f58])).
% 3.12/0.80  fof(f58,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f31])).
% 3.12/0.80  fof(f4115,plain,(
% 3.12/0.80    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f4114])).
% 3.12/0.80  fof(f4114,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149)),
% 3.12/0.80    inference(resolution,[],[f3918,f211])).
% 3.12/0.80  fof(f211,plain,(
% 3.12/0.80    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)) ) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f189,f117])).
% 3.12/0.80  fof(f117,plain,(
% 3.12/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_10),
% 3.12/0.80    inference(avatar_component_clause,[],[f115])).
% 3.12/0.80  fof(f189,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 3.12/0.80    inference(resolution,[],[f63,f59])).
% 3.12/0.80  fof(f59,plain,(
% 3.12/0.80    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f31])).
% 3.12/0.80  fof(f63,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f33])).
% 3.12/0.80  fof(f33,plain,(
% 3.12/0.80    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.12/0.80    inference(flattening,[],[f32])).
% 3.12/0.80  fof(f32,plain,(
% 3.12/0.80    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.12/0.80    inference(ennf_transformation,[],[f5])).
% 3.12/0.80  fof(f5,axiom,(
% 3.12/0.80    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.12/0.80  fof(f3918,plain,(
% 3.12/0.80    ( ! [X0] : (~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))) ) | (~spl9_10 | ~spl9_16 | ~spl9_149)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f3917])).
% 3.12/0.80  fof(f3917,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16 | ~spl9_149)),
% 3.12/0.80    inference(resolution,[],[f1019,f1118])).
% 3.12/0.80  fof(f1118,plain,(
% 3.12/0.80    ( ! [X0] : (m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0)) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f1117])).
% 3.12/0.80  fof(f1117,plain,(
% 3.12/0.80    ( ! [X0] : (m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_16)),
% 3.12/0.80    inference(resolution,[],[f325,f59])).
% 3.12/0.80  fof(f325,plain,(
% 3.12/0.80    ( ! [X1] : (~r2_hidden(sK4(sK1,X1),sK1) | m1_connsp_2(sK3(sK4(sK1,X1)),sK0,sK4(sK1,X1)) | r1_tarski(sK1,X1)) ) | (~spl9_10 | ~spl9_16)),
% 3.12/0.80    inference(resolution,[],[f211,f143])).
% 3.12/0.80  fof(f143,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1)) ) | ~spl9_16),
% 3.12/0.80    inference(avatar_component_clause,[],[f142])).
% 3.12/0.80  fof(f1019,plain,(
% 3.12/0.80    ( ! [X8,X7] : (~m1_connsp_2(sK3(sK4(sK1,X7)),sK0,X8) | r1_tarski(sK1,X7) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r2_hidden(X8,k1_tops_1(sK0,sK3(sK4(sK1,X7))))) ) | ~spl9_149),
% 3.12/0.80    inference(avatar_component_clause,[],[f1018])).
% 3.12/0.80  fof(f4139,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | ~spl9_512),
% 3.12/0.80    inference(avatar_component_clause,[],[f4138])).
% 3.12/0.80  fof(f4140,plain,(
% 3.12/0.80    ~spl9_10 | spl9_512 | ~spl9_10 | ~spl9_15 | ~spl9_147),
% 3.12/0.80    inference(avatar_split_clause,[],[f4136,f1010,f138,f115,f4138,f115])).
% 3.12/0.80  fof(f138,plain,(
% 3.12/0.80    spl9_15 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 3.12/0.80  fof(f1010,plain,(
% 3.12/0.80    spl9_147 <=> ! [X3,X4] : (r1_tarski(sK1,X3) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),k1_tops_1(sK0,X4)) | ~r1_tarski(sK3(sK4(sK1,X3)),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).
% 3.12/0.80  fof(f4136,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl9_10 | ~spl9_15 | ~spl9_147)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f4132])).
% 3.12/0.80  fof(f4132,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_15 | ~spl9_147)),
% 3.12/0.80    inference(resolution,[],[f1011,f976])).
% 3.12/0.80  fof(f976,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(sK3(sK4(sK1,X0)),sK1) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_15)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f975])).
% 3.12/0.80  fof(f975,plain,(
% 3.12/0.80    ( ! [X0] : (r1_tarski(sK3(sK4(sK1,X0)),sK1) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_15)),
% 3.12/0.80    inference(resolution,[],[f326,f59])).
% 3.12/0.80  fof(f326,plain,(
% 3.12/0.80    ( ! [X2] : (~r2_hidden(sK4(sK1,X2),sK1) | r1_tarski(sK3(sK4(sK1,X2)),sK1) | r1_tarski(sK1,X2)) ) | (~spl9_10 | ~spl9_15)),
% 3.12/0.80    inference(resolution,[],[f211,f139])).
% 3.12/0.80  fof(f139,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl9_15),
% 3.12/0.80    inference(avatar_component_clause,[],[f138])).
% 3.12/0.80  fof(f1011,plain,(
% 3.12/0.80    ( ! [X4,X3] : (~r1_tarski(sK3(sK4(sK1,X3)),X4) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),k1_tops_1(sK0,X4)) | r1_tarski(sK1,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl9_147),
% 3.12/0.80    inference(avatar_component_clause,[],[f1010])).
% 3.12/0.80  fof(f2370,plain,(
% 3.12/0.80    spl9_27 | ~spl9_25 | ~spl9_40 | ~spl9_42),
% 3.12/0.80    inference(avatar_split_clause,[],[f2366,f336,f321,f216,f230])).
% 3.12/0.80  fof(f216,plain,(
% 3.12/0.80    spl9_25 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 3.12/0.80  fof(f321,plain,(
% 3.12/0.80    spl9_40 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1) | ~m1_connsp_2(sK1,sK0,X3))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 3.12/0.80  fof(f336,plain,(
% 3.12/0.80    spl9_42 <=> ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X3) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 3.12/0.80  fof(f2366,plain,(
% 3.12/0.80    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl9_25 | ~spl9_40 | ~spl9_42)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f2363])).
% 3.12/0.80  fof(f2363,plain,(
% 3.12/0.80    r1_tarski(k1_tops_1(sK0,sK1),sK1) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl9_25 | ~spl9_40 | ~spl9_42)),
% 3.12/0.80    inference(resolution,[],[f2359,f60])).
% 3.12/0.80  fof(f2359,plain,(
% 3.12/0.80    ( ! [X0] : (r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl9_25 | ~spl9_40 | ~spl9_42)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f2358])).
% 3.12/0.80  fof(f2358,plain,(
% 3.12/0.80    ( ! [X0] : (r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl9_25 | ~spl9_40 | ~spl9_42)),
% 3.12/0.80    inference(resolution,[],[f973,f223])).
% 3.12/0.80  fof(f223,plain,(
% 3.12/0.80    ( ! [X0] : (m1_subset_1(sK4(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl9_25),
% 3.12/0.80    inference(resolution,[],[f218,f189])).
% 3.12/0.80  fof(f218,plain,(
% 3.12/0.80    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_25),
% 3.12/0.80    inference(avatar_component_clause,[],[f216])).
% 3.12/0.80  fof(f973,plain,(
% 3.12/0.80    ( ! [X1] : (~m1_subset_1(sK4(k1_tops_1(sK0,sK1),X1),u1_struct_0(sK0)) | r2_hidden(sK4(k1_tops_1(sK0,sK1),X1),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X1)) ) | (~spl9_25 | ~spl9_40 | ~spl9_42)),
% 3.12/0.80    inference(resolution,[],[f703,f322])).
% 3.12/0.80  fof(f322,plain,(
% 3.12/0.80    ( ! [X3] : (~m1_connsp_2(sK1,sK0,X3) | r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl9_40),
% 3.12/0.80    inference(avatar_component_clause,[],[f321])).
% 3.12/0.80  fof(f703,plain,(
% 3.12/0.80    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl9_25 | ~spl9_42)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f702])).
% 3.12/0.80  fof(f702,plain,(
% 3.12/0.80    ( ! [X0] : (m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl9_25 | ~spl9_42)),
% 3.12/0.80    inference(resolution,[],[f437,f223])).
% 3.12/0.80  fof(f437,plain,(
% 3.12/0.80    ( ! [X0] : (~m1_subset_1(sK4(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,sK4(k1_tops_1(sK0,sK1),X0)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl9_42),
% 3.12/0.80    inference(resolution,[],[f337,f59])).
% 3.12/0.80  fof(f337,plain,(
% 3.12/0.80    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl9_42),
% 3.12/0.80    inference(avatar_component_clause,[],[f336])).
% 3.12/0.80  fof(f1786,plain,(
% 3.12/0.80    spl9_9 | ~spl9_7 | ~spl9_8 | spl9_149 | ~spl9_10 | ~spl9_17),
% 3.12/0.80    inference(avatar_split_clause,[],[f1774,f146,f115,f1018,f105,f100,f110])).
% 3.12/0.80  fof(f110,plain,(
% 3.12/0.80    spl9_9 <=> v2_struct_0(sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 3.12/0.80  fof(f100,plain,(
% 3.12/0.80    spl9_7 <=> l1_pre_topc(sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.12/0.80  fof(f105,plain,(
% 3.12/0.80    spl9_8 <=> v2_pre_topc(sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 3.12/0.80  fof(f146,plain,(
% 3.12/0.80    spl9_17 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 3.12/0.80  fof(f1774,plain,(
% 3.12/0.80    ( ! [X6,X7] : (r1_tarski(sK1,X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X7,k1_tops_1(sK0,sK3(sK4(sK1,X6)))) | ~m1_connsp_2(sK3(sK4(sK1,X6)),sK0,X7)) ) | (~spl9_10 | ~spl9_17)),
% 3.12/0.80    inference(resolution,[],[f993,f48])).
% 3.12/0.80  fof(f48,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f20])).
% 3.12/0.80  fof(f20,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.12/0.80    inference(flattening,[],[f19])).
% 3.12/0.80  fof(f19,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f9])).
% 3.12/0.80  fof(f9,axiom,(
% 3.12/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 3.12/0.80  fof(f993,plain,(
% 3.12/0.80    ( ! [X0] : (m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_17)),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f992])).
% 3.12/0.80  fof(f992,plain,(
% 3.12/0.80    ( ! [X0] : (m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_17)),
% 3.12/0.80    inference(resolution,[],[f324,f59])).
% 3.12/0.80  fof(f324,plain,(
% 3.12/0.80    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK1) | m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl9_10 | ~spl9_17)),
% 3.12/0.80    inference(resolution,[],[f211,f147])).
% 3.12/0.80  fof(f147,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1)) ) | ~spl9_17),
% 3.12/0.80    inference(avatar_component_clause,[],[f146])).
% 3.12/0.80  fof(f1784,plain,(
% 3.12/0.80    ~spl9_7 | spl9_147 | ~spl9_10 | ~spl9_17),
% 3.12/0.80    inference(avatar_split_clause,[],[f1772,f146,f115,f1010,f100])).
% 3.12/0.80  fof(f1772,plain,(
% 3.12/0.80    ( ! [X2,X3] : (r1_tarski(sK1,X2) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3(sK4(sK1,X2)),X3) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3))) ) | (~spl9_10 | ~spl9_17)),
% 3.12/0.80    inference(resolution,[],[f993,f46])).
% 3.12/0.80  fof(f46,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 3.12/0.80    inference(cnf_transformation,[],[f18])).
% 3.12/0.80  fof(f18,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.12/0.80    inference(flattening,[],[f17])).
% 3.12/0.80  fof(f17,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.12/0.80    inference(ennf_transformation,[],[f7])).
% 3.12/0.80  fof(f7,axiom,(
% 3.12/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 3.12/0.80  fof(f1512,plain,(
% 3.12/0.80    ~spl9_7 | ~spl9_2 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f1501,f115,f80,f100])).
% 3.12/0.80  fof(f80,plain,(
% 3.12/0.80    spl9_2 <=> ! [X1,X3] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.12/0.80  fof(f1501,plain,(
% 3.12/0.80    ~l1_pre_topc(sK0) | (~spl9_2 | ~spl9_10)),
% 3.12/0.80    inference(resolution,[],[f81,f117])).
% 3.12/0.80  fof(f81,plain,(
% 3.12/0.80    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl9_2),
% 3.12/0.80    inference(avatar_component_clause,[],[f80])).
% 3.12/0.80  fof(f1442,plain,(
% 3.12/0.80    ~spl9_7 | ~spl9_11 | spl9_33 | ~spl9_5 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f275,f115,f92,f261,f120,f100])).
% 3.12/0.80  fof(f120,plain,(
% 3.12/0.80    spl9_11 <=> v3_pre_topc(sK1,sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 3.12/0.80  fof(f92,plain,(
% 3.12/0.80    spl9_5 <=> ! [X1,X3] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.12/0.80  fof(f275,plain,(
% 3.12/0.80    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl9_5 | ~spl9_10)),
% 3.12/0.80    inference(resolution,[],[f93,f117])).
% 3.12/0.80  fof(f93,plain,(
% 3.12/0.80    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~l1_pre_topc(X1)) ) | ~spl9_5),
% 3.12/0.80    inference(avatar_component_clause,[],[f92])).
% 3.12/0.80  fof(f1437,plain,(
% 3.12/0.80    sK1 != k1_tops_1(sK0,sK1) | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 3.12/0.80    introduced(theory_tautology_sat_conflict,[])).
% 3.12/0.80  fof(f1319,plain,(
% 3.12/0.80    ~spl9_7 | ~spl9_8 | ~spl9_6 | ~spl9_19),
% 3.12/0.80    inference(avatar_split_clause,[],[f1317,f161,f96,f105,f100])).
% 3.12/0.80  fof(f96,plain,(
% 3.12/0.80    spl9_6 <=> ! [X0] : (~v2_pre_topc(X0) | ~sP5(X0) | ~l1_pre_topc(X0))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 3.12/0.80  fof(f161,plain,(
% 3.12/0.80    spl9_19 <=> sP5(sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 3.12/0.80  fof(f1317,plain,(
% 3.12/0.80    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl9_6 | ~spl9_19)),
% 3.12/0.80    inference(resolution,[],[f97,f163])).
% 3.12/0.80  fof(f163,plain,(
% 3.12/0.80    sP5(sK0) | ~spl9_19),
% 3.12/0.80    inference(avatar_component_clause,[],[f161])).
% 3.12/0.80  fof(f97,plain,(
% 3.12/0.80    ( ! [X0] : (~sP5(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl9_6),
% 3.12/0.80    inference(avatar_component_clause,[],[f96])).
% 3.12/0.80  fof(f1062,plain,(
% 3.12/0.80    ~spl9_7 | ~spl9_8 | ~spl9_3 | ~spl9_30),
% 3.12/0.80    inference(avatar_split_clause,[],[f1061,f248,f84,f105,f100])).
% 3.12/0.80  fof(f84,plain,(
% 3.12/0.80    spl9_3 <=> ! [X0] : (~v2_pre_topc(X0) | ~sP7(X0) | ~l1_pre_topc(X0))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.12/0.80  fof(f248,plain,(
% 3.12/0.80    spl9_30 <=> sP7(sK0)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 3.12/0.80  fof(f1061,plain,(
% 3.12/0.80    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl9_3 | ~spl9_30)),
% 3.12/0.80    inference(resolution,[],[f250,f85])).
% 3.12/0.80  fof(f85,plain,(
% 3.12/0.80    ( ! [X0] : (~sP7(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl9_3),
% 3.12/0.80    inference(avatar_component_clause,[],[f84])).
% 3.12/0.80  fof(f250,plain,(
% 3.12/0.80    sP7(sK0) | ~spl9_30),
% 3.12/0.80    inference(avatar_component_clause,[],[f248])).
% 3.12/0.80  fof(f1048,plain,(
% 3.12/0.80    ~spl9_11 | spl9_156 | spl9_9 | ~spl9_7 | ~spl9_8 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f410,f115,f105,f100,f110,f1046,f120])).
% 3.12/0.80  fof(f410,plain,(
% 3.12/0.80    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~r2_hidden(X4,sK1) | m1_connsp_2(sK1,sK0,X4)) ) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f50,f117])).
% 3.12/0.80  fof(f50,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f24])).
% 3.12/0.80  fof(f24,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.12/0.80    inference(flattening,[],[f23])).
% 3.12/0.80  fof(f23,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f11])).
% 3.12/0.80  fof(f11,axiom,(
% 3.12/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 3.12/0.80  fof(f338,plain,(
% 3.12/0.80    spl9_9 | spl9_42 | ~spl9_7 | ~spl9_8 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f329,f115,f105,f100,f336,f110])).
% 3.12/0.80  fof(f329,plain,(
% 3.12/0.80    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X3)) ) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f47,f117])).
% 3.12/0.80  fof(f47,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f20])).
% 3.12/0.80  fof(f323,plain,(
% 3.12/0.80    spl9_40 | spl9_9 | ~spl9_7 | ~spl9_8 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f314,f115,f105,f100,f110,f321])).
% 3.12/0.80  fof(f314,plain,(
% 3.12/0.80    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_connsp_2(sK1,sK0,X3) | r2_hidden(X3,sK1)) ) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f49,f117])).
% 3.12/0.80  fof(f49,plain,(
% 3.12/0.80    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f22])).
% 3.12/0.80  fof(f22,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.12/0.80    inference(flattening,[],[f21])).
% 3.12/0.80  fof(f21,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f12])).
% 3.12/0.80  fof(f12,axiom,(
% 3.12/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 3.12/0.80  fof(f264,plain,(
% 3.12/0.80    spl9_30 | spl9_11 | ~spl9_33 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f246,f115,f261,f120,f248])).
% 3.12/0.80  fof(f246,plain,(
% 3.12/0.80    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | sP7(sK0) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f71,f117])).
% 3.12/0.80  fof(f71,plain,(
% 3.12/0.80    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | sP7(X0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f71_D])).
% 3.12/0.80  fof(f71_D,plain,(
% 3.12/0.80    ( ! [X0] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) ) <=> ~sP7(X0)) )),
% 3.12/0.80    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 3.12/0.80  fof(f233,plain,(
% 3.12/0.80    ~spl9_26 | ~spl9_27 | ~spl9_14 | ~spl9_25),
% 3.12/0.80    inference(avatar_split_clause,[],[f220,f216,f134,f230,f226])).
% 3.12/0.80  fof(f226,plain,(
% 3.12/0.80    spl9_26 <=> m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2)),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 3.12/0.80  fof(f134,plain,(
% 3.12/0.80    spl9_14 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 3.12/0.80  fof(f220,plain,(
% 3.12/0.80    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_connsp_2(k1_tops_1(sK0,sK1),sK0,sK2) | (~spl9_14 | ~spl9_25)),
% 3.12/0.80    inference(resolution,[],[f218,f135])).
% 3.12/0.80  fof(f135,plain,(
% 3.12/0.80    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl9_14),
% 3.12/0.80    inference(avatar_component_clause,[],[f134])).
% 3.12/0.80  fof(f219,plain,(
% 3.12/0.80    spl9_25 | ~spl9_7 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f213,f115,f100,f216])).
% 3.12/0.80  fof(f213,plain,(
% 3.12/0.80    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f54,f117])).
% 3.12/0.80  fof(f54,plain,(
% 3.12/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.12/0.80    inference(cnf_transformation,[],[f30])).
% 3.12/0.80  fof(f30,plain,(
% 3.12/0.80    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.12/0.80    inference(flattening,[],[f29])).
% 3.12/0.80  fof(f29,plain,(
% 3.12/0.80    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f6])).
% 3.12/0.80  fof(f6,axiom,(
% 3.12/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 3.12/0.80  fof(f164,plain,(
% 3.12/0.80    spl9_19 | ~spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f158,f115,f161])).
% 3.12/0.80  fof(f158,plain,(
% 3.12/0.80    sP5(sK0) | ~spl9_10),
% 3.12/0.80    inference(resolution,[],[f67,f117])).
% 3.12/0.80  fof(f67,plain,(
% 3.12/0.80    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f67_D])).
% 3.12/0.80  fof(f67_D,plain,(
% 3.12/0.80    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP5(X0)) )),
% 3.12/0.80    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 3.12/0.80  fof(f148,plain,(
% 3.12/0.80    spl9_11 | spl9_17),
% 3.12/0.80    inference(avatar_split_clause,[],[f36,f146,f120])).
% 3.12/0.80  fof(f36,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f16,plain,(
% 3.12/0.80    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.12/0.80    inference(flattening,[],[f15])).
% 3.12/0.80  fof(f15,plain,(
% 3.12/0.80    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f14])).
% 3.12/0.80  fof(f14,negated_conjecture,(
% 3.12/0.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.12/0.80    inference(negated_conjecture,[],[f13])).
% 3.12/0.80  fof(f13,conjecture,(
% 3.12/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 3.12/0.80  fof(f144,plain,(
% 3.12/0.80    spl9_11 | spl9_16),
% 3.12/0.80    inference(avatar_split_clause,[],[f37,f142,f120])).
% 3.12/0.80  fof(f37,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f140,plain,(
% 3.12/0.80    spl9_11 | spl9_15),
% 3.12/0.80    inference(avatar_split_clause,[],[f38,f138,f120])).
% 3.12/0.80  fof(f38,plain,(
% 3.12/0.80    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f136,plain,(
% 3.12/0.80    ~spl9_11 | spl9_14),
% 3.12/0.80    inference(avatar_split_clause,[],[f39,f134,f120])).
% 3.12/0.80  fof(f39,plain,(
% 3.12/0.80    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f132,plain,(
% 3.12/0.80    ~spl9_11 | spl9_13),
% 3.12/0.80    inference(avatar_split_clause,[],[f40,f129,f120])).
% 3.12/0.80  fof(f40,plain,(
% 3.12/0.80    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f127,plain,(
% 3.12/0.80    ~spl9_11 | spl9_12),
% 3.12/0.80    inference(avatar_split_clause,[],[f41,f124,f120])).
% 3.12/0.80  fof(f41,plain,(
% 3.12/0.80    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f118,plain,(
% 3.12/0.80    spl9_10),
% 3.12/0.80    inference(avatar_split_clause,[],[f42,f115])).
% 3.12/0.80  fof(f42,plain,(
% 3.12/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f113,plain,(
% 3.12/0.80    ~spl9_9),
% 3.12/0.80    inference(avatar_split_clause,[],[f43,f110])).
% 3.12/0.80  fof(f43,plain,(
% 3.12/0.80    ~v2_struct_0(sK0)),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f108,plain,(
% 3.12/0.80    spl9_8),
% 3.12/0.80    inference(avatar_split_clause,[],[f44,f105])).
% 3.12/0.80  fof(f44,plain,(
% 3.12/0.80    v2_pre_topc(sK0)),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f103,plain,(
% 3.12/0.80    spl9_7),
% 3.12/0.80    inference(avatar_split_clause,[],[f45,f100])).
% 3.12/0.80  fof(f45,plain,(
% 3.12/0.80    l1_pre_topc(sK0)),
% 3.12/0.80    inference(cnf_transformation,[],[f16])).
% 3.12/0.80  fof(f98,plain,(
% 3.12/0.80    spl9_4 | spl9_6),
% 3.12/0.80    inference(avatar_split_clause,[],[f69,f96,f88])).
% 3.12/0.80  fof(f88,plain,(
% 3.12/0.80    spl9_4 <=> sP6),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 3.12/0.80  fof(f69,plain,(
% 3.12/0.80    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP5(X0) | sP6) )),
% 3.12/0.80    inference(cnf_transformation,[],[f69_D])).
% 3.12/0.80  fof(f69_D,plain,(
% 3.12/0.80    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP5(X0)) ) <=> ~sP6),
% 3.12/0.80    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 3.12/0.80  fof(f94,plain,(
% 3.12/0.80    ~spl9_4 | spl9_5),
% 3.12/0.80    inference(avatar_split_clause,[],[f70,f92,f88])).
% 3.12/0.80  fof(f70,plain,(
% 3.12/0.80    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~sP6) )),
% 3.12/0.80    inference(general_splitting,[],[f68,f69_D])).
% 3.12/0.80  fof(f68,plain,(
% 3.12/0.80    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~sP5(X0)) )),
% 3.12/0.80    inference(general_splitting,[],[f52,f67_D])).
% 3.12/0.80  fof(f52,plain,(
% 3.12/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 3.12/0.80    inference(cnf_transformation,[],[f26])).
% 3.12/0.80  fof(f26,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.12/0.80    inference(flattening,[],[f25])).
% 3.12/0.80  fof(f25,plain,(
% 3.12/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f8])).
% 3.12/0.80  fof(f8,axiom,(
% 3.12/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 3.12/0.80  fof(f86,plain,(
% 3.12/0.80    spl9_1 | spl9_3),
% 3.12/0.80    inference(avatar_split_clause,[],[f73,f84,f76])).
% 3.12/0.80  fof(f76,plain,(
% 3.12/0.80    spl9_1 <=> sP8),
% 3.12/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.12/0.80  fof(f73,plain,(
% 3.12/0.80    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP7(X0) | sP8) )),
% 3.12/0.80    inference(cnf_transformation,[],[f73_D])).
% 3.12/0.80  fof(f73_D,plain,(
% 3.12/0.80    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP7(X0)) ) <=> ~sP8),
% 3.12/0.80    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 3.12/0.80  fof(f82,plain,(
% 3.12/0.80    ~spl9_1 | spl9_2),
% 3.12/0.80    inference(avatar_split_clause,[],[f74,f80,f76])).
% 3.12/0.80  fof(f74,plain,(
% 3.12/0.80    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~sP8) )),
% 3.12/0.80    inference(general_splitting,[],[f72,f73_D])).
% 3.12/0.80  fof(f72,plain,(
% 3.12/0.80    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~sP7(X0)) )),
% 3.12/0.80    inference(general_splitting,[],[f51,f71_D])).
% 3.12/0.80  fof(f51,plain,(
% 3.12/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f26])).
% 3.12/0.80  % SZS output end Proof for theBenchmark
% 3.12/0.80  % (15614)------------------------------
% 3.12/0.80  % (15614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.80  % (15614)Termination reason: Refutation
% 3.12/0.80  
% 3.12/0.80  % (15614)Memory used [KB]: 13944
% 3.12/0.80  % (15614)Time elapsed: 0.323 s
% 3.12/0.80  % (15614)------------------------------
% 3.12/0.80  % (15614)------------------------------
% 3.12/0.80  % (15591)Success in time 0.438 s
%------------------------------------------------------------------------------
