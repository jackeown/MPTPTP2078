%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 319 expanded)
%              Number of leaves         :   32 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  559 (1313 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f89,f94,f98,f102,f106,f110,f150,f176,f239,f611,f623,f1567,f1887,f1888,f1896,f1960,f2187,f2212,f2246,f2248])).

fof(f2248,plain,(
    spl5_195 ),
    inference(avatar_contradiction_clause,[],[f2247])).

fof(f2247,plain,
    ( $false
    | spl5_195 ),
    inference(resolution,[],[f1959,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1959,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_195 ),
    inference(avatar_component_clause,[],[f1957])).

fof(f1957,plain,
    ( spl5_195
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).

fof(f2246,plain,
    ( ~ spl5_195
    | spl5_17
    | ~ spl5_4
    | ~ spl5_187 ),
    inference(avatar_split_clause,[],[f2236,f1894,f77,f160,f1957])).

fof(f160,plain,
    ( spl5_17
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f77,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1894,plain,
    ( spl5_187
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f2236,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl5_4
    | ~ spl5_187 ),
    inference(resolution,[],[f1895,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f1895,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_187 ),
    inference(avatar_component_clause,[],[f1894])).

fof(f2212,plain,
    ( ~ spl5_17
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f2210,f156,f147,f160])).

fof(f147,plain,
    ( spl5_15
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f156,plain,
    ( spl5_16
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f2210,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl5_16 ),
    inference(extensionality_resolution,[],[f51,f157])).

fof(f157,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2187,plain,
    ( ~ spl5_6
    | spl5_194
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f2182,f237,f156,f91,f1953,f86])).

fof(f86,plain,
    ( spl5_6
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1953,plain,
    ( spl5_194
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f91,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f237,plain,
    ( spl5_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f2182,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(resolution,[],[f2006,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f2006,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f238,f158])).

fof(f158,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f237])).

fof(f1960,plain,
    ( ~ spl5_194
    | ~ spl5_195
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1928,f96,f77,f1957,f1953])).

fof(f96,plain,
    ( spl5_8
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1928,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(resolution,[],[f97,f79])).

fof(f97,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1896,plain,
    ( ~ spl5_5
    | spl5_187
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f226,f77,f62,f1894,f82])).

fof(f82,plain,
    ( spl5_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f62,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f44,f79])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f1888,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1887,plain,
    ( spl5_17
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1886,f1565,f621,f104,f77,f160])).

fof(f104,plain,
    ( spl5_10
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f621,plain,
    ( spl5_79
  <=> ! [X9,X8] :
        ( r1_tarski(sK1,X8)
        | ~ m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f1565,plain,
    ( spl5_167
  <=> ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f1886,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1883])).

fof(f1883,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79
    | ~ spl5_167 ),
    inference(resolution,[],[f1879,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f1879,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1,X1),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X1) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79
    | ~ spl5_167 ),
    inference(duplicate_literal_removal,[],[f1871])).

fof(f1871,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1,X1),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79
    | ~ spl5_167 ),
    inference(resolution,[],[f1865,f1566])).

fof(f1566,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1865,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),X4)
        | r2_hidden(sK4(sK1,X3),X4)
        | r1_tarski(sK1,X3) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79 ),
    inference(resolution,[],[f1862,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1862,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79 ),
    inference(duplicate_literal_removal,[],[f1861])).

fof(f1861,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79 ),
    inference(resolution,[],[f1524,f279])).

fof(f279,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f137,f79])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f1524,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79 ),
    inference(duplicate_literal_removal,[],[f1523])).

fof(f1523,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_79 ),
    inference(resolution,[],[f622,f576])).

fof(f576,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f334,f53])).

fof(f334,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,X1),sK1)
        | m1_connsp_2(sK3(sK4(sK1,X1)),sK0,sK4(sK1,X1))
        | r1_tarski(sK1,X1) )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f279,f105])).

fof(f105,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f622,plain,
    ( ! [X8,X9] :
        ( ~ m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9)
        | r1_tarski(sK1,X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8)))) )
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f621])).

fof(f1567,plain,
    ( ~ spl5_4
    | spl5_167
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1563,f609,f100,f77,f1565,f77])).

fof(f100,plain,
    ( spl5_9
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f609,plain,
    ( spl5_76
  <=> ! [X3,X2] :
        ( r1_tarski(sK1,X2)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3))
        | ~ r1_tarski(sK3(sK4(sK1,X2)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1563,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_76 ),
    inference(duplicate_literal_removal,[],[f1559])).

fof(f1559,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_76 ),
    inference(resolution,[],[f610,f478])).

fof(f478,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK4(sK1,X0)),sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK4(sK1,X0)),sK1)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f335,f53])).

fof(f335,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(sK1,X2),sK1)
        | r1_tarski(sK3(sK4(sK1,X2)),sK1)
        | r1_tarski(sK1,X2) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f279,f101])).

fof(f101,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f610,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK3(sK4(sK1,X2)),X3)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3))
        | r1_tarski(sK1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f609])).

fof(f623,plain,
    ( spl5_3
    | ~ spl5_1
    | ~ spl5_2
    | spl5_79
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f598,f108,f77,f621,f67,f62,f72])).

fof(f72,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f67,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( spl5_11
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f598,plain,
    ( ! [X8,X9] :
        ( r1_tarski(sK1,X8)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8))))
        | ~ m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f515,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f515,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f333,f53])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK1)
        | m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f279,f109])).

fof(f109,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f611,plain,
    ( ~ spl5_1
    | spl5_76
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f595,f108,f77,f609,f62])).

fof(f595,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK1,X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3(sK4(sK1,X2)),X3)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3)) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f515,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f239,plain,
    ( spl5_3
    | spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f233,f77,f67,f62,f237,f72])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f45,f79])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f170,f77,f62,f67,f173])).

fof(f173,plain,
    ( spl5_19
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f170,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f48,f79])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f150,plain,
    ( spl5_15
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f144,f77,f62,f147])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f42,f79])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f110,plain,
    ( spl5_5
    | spl5_11 ),
    inference(avatar_split_clause,[],[f32,f108,f82])).

fof(f32,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f106,plain,
    ( spl5_5
    | spl5_10 ),
    inference(avatar_split_clause,[],[f33,f104,f82])).

fof(f33,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,
    ( spl5_5
    | spl5_9 ),
    inference(avatar_split_clause,[],[f34,f100,f82])).

fof(f34,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,
    ( ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f35,f96,f82])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( ~ spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f36,f91,f82])).

fof(f36,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f37,f86,f82])).

fof(f37,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f38,f77])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f67])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f41,f62])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:43:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (24290)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.50  % (24282)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (24267)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24276)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (24269)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (24274)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (24283)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (24286)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (24284)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (24275)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (24264)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (24277)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (24268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (24271)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (24262)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (24263)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (24265)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (24272)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (24287)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (24266)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (24287)Refutation not found, incomplete strategy% (24287)------------------------------
% 0.22/0.55  % (24287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24287)Memory used [KB]: 10746
% 0.22/0.55  % (24287)Time elapsed: 0.132 s
% 0.22/0.55  % (24287)------------------------------
% 0.22/0.55  % (24287)------------------------------
% 0.22/0.55  % (24273)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (24285)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (24280)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (24261)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (24281)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (24279)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (24270)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.56  % (24289)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (24288)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.56  % (24278)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.10/0.69  % (24277)Refutation found. Thanks to Tanya!
% 2.10/0.69  % SZS status Theorem for theBenchmark
% 2.10/0.69  % (24328)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.69  % SZS output start Proof for theBenchmark
% 2.10/0.69  fof(f2249,plain,(
% 2.10/0.69    $false),
% 2.10/0.69    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f89,f94,f98,f102,f106,f110,f150,f176,f239,f611,f623,f1567,f1887,f1888,f1896,f1960,f2187,f2212,f2246,f2248])).
% 2.10/0.69  fof(f2248,plain,(
% 2.10/0.69    spl5_195),
% 2.10/0.69    inference(avatar_contradiction_clause,[],[f2247])).
% 2.10/0.69  fof(f2247,plain,(
% 2.10/0.69    $false | spl5_195),
% 2.10/0.69    inference(resolution,[],[f1959,f59])).
% 2.10/0.69  fof(f59,plain,(
% 2.10/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/0.69    inference(equality_resolution,[],[f50])).
% 2.10/0.69  fof(f50,plain,(
% 2.10/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.10/0.69    inference(cnf_transformation,[],[f2])).
% 2.10/0.69  fof(f2,axiom,(
% 2.10/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.69  fof(f1959,plain,(
% 2.10/0.69    ~r1_tarski(sK1,sK1) | spl5_195),
% 2.10/0.69    inference(avatar_component_clause,[],[f1957])).
% 2.10/0.69  fof(f1957,plain,(
% 2.10/0.69    spl5_195 <=> r1_tarski(sK1,sK1)),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).
% 2.10/0.69  fof(f2246,plain,(
% 2.10/0.69    ~spl5_195 | spl5_17 | ~spl5_4 | ~spl5_187),
% 2.10/0.69    inference(avatar_split_clause,[],[f2236,f1894,f77,f160,f1957])).
% 2.10/0.69  fof(f160,plain,(
% 2.10/0.69    spl5_17 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.10/0.69  fof(f77,plain,(
% 2.10/0.69    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.10/0.69  fof(f1894,plain,(
% 2.10/0.69    spl5_187 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK1,X0))),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).
% 2.10/0.69  fof(f2236,plain,(
% 2.10/0.69    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl5_4 | ~spl5_187)),
% 2.10/0.69    inference(resolution,[],[f1895,f79])).
% 2.10/0.69  fof(f79,plain,(
% 2.10/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 2.10/0.69    inference(avatar_component_clause,[],[f77])).
% 2.10/0.69  fof(f1895,plain,(
% 2.10/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK1,X0)) ) | ~spl5_187),
% 2.10/0.69    inference(avatar_component_clause,[],[f1894])).
% 2.10/0.69  fof(f2212,plain,(
% 2.10/0.69    ~spl5_17 | ~spl5_15 | spl5_16),
% 2.10/0.69    inference(avatar_split_clause,[],[f2210,f156,f147,f160])).
% 2.10/0.69  fof(f147,plain,(
% 2.10/0.69    spl5_15 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.10/0.69  fof(f156,plain,(
% 2.10/0.69    spl5_16 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.10/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.10/0.69  fof(f2210,plain,(
% 2.10/0.69    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl5_16),
% 2.10/0.69    inference(extensionality_resolution,[],[f51,f157])).
% 2.10/0.70  fof(f157,plain,(
% 2.10/0.70    sK1 != k1_tops_1(sK0,sK1) | spl5_16),
% 2.10/0.70    inference(avatar_component_clause,[],[f156])).
% 2.10/0.70  fof(f51,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f2])).
% 2.10/0.70  fof(f2187,plain,(
% 2.10/0.70    ~spl5_6 | spl5_194 | ~spl5_7 | ~spl5_16 | ~spl5_29),
% 2.10/0.70    inference(avatar_split_clause,[],[f2182,f237,f156,f91,f1953,f86])).
% 2.10/0.70  fof(f86,plain,(
% 2.10/0.70    spl5_6 <=> r2_hidden(sK2,sK1)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.10/0.70  fof(f1953,plain,(
% 2.10/0.70    spl5_194 <=> m1_connsp_2(sK1,sK0,sK2)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).
% 2.10/0.70  fof(f91,plain,(
% 2.10/0.70    spl5_7 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.10/0.70  fof(f237,plain,(
% 2.10/0.70    spl5_29 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.10/0.70  fof(f2182,plain,(
% 2.10/0.70    m1_connsp_2(sK1,sK0,sK2) | ~r2_hidden(sK2,sK1) | (~spl5_7 | ~spl5_16 | ~spl5_29)),
% 2.10/0.70    inference(resolution,[],[f2006,f93])).
% 2.10/0.70  fof(f93,plain,(
% 2.10/0.70    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_7),
% 2.10/0.70    inference(avatar_component_clause,[],[f91])).
% 2.10/0.70  fof(f2006,plain,(
% 2.10/0.70    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X0) | ~r2_hidden(X0,sK1)) ) | (~spl5_16 | ~spl5_29)),
% 2.10/0.70    inference(backward_demodulation,[],[f238,f158])).
% 2.10/0.70  fof(f158,plain,(
% 2.10/0.70    sK1 = k1_tops_1(sK0,sK1) | ~spl5_16),
% 2.10/0.70    inference(avatar_component_clause,[],[f156])).
% 2.10/0.70  fof(f238,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_29),
% 2.10/0.70    inference(avatar_component_clause,[],[f237])).
% 2.10/0.70  fof(f1960,plain,(
% 2.10/0.70    ~spl5_194 | ~spl5_195 | ~spl5_4 | ~spl5_8),
% 2.10/0.70    inference(avatar_split_clause,[],[f1928,f96,f77,f1957,f1953])).
% 2.10/0.70  fof(f96,plain,(
% 2.10/0.70    spl5_8 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.10/0.70  fof(f1928,plain,(
% 2.10/0.70    ~r1_tarski(sK1,sK1) | ~m1_connsp_2(sK1,sK0,sK2) | (~spl5_4 | ~spl5_8)),
% 2.10/0.70    inference(resolution,[],[f97,f79])).
% 2.10/0.70  fof(f97,plain,(
% 2.10/0.70    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl5_8),
% 2.10/0.70    inference(avatar_component_clause,[],[f96])).
% 2.10/0.70  fof(f1896,plain,(
% 2.10/0.70    ~spl5_5 | spl5_187 | ~spl5_1 | ~spl5_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f226,f77,f62,f1894,f82])).
% 2.10/0.70  fof(f82,plain,(
% 2.10/0.70    spl5_5 <=> v3_pre_topc(sK1,sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.10/0.70  fof(f62,plain,(
% 2.10/0.70    spl5_1 <=> l1_pre_topc(sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.10/0.70  fof(f226,plain,(
% 2.10/0.70    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | ~spl5_4),
% 2.10/0.70    inference(resolution,[],[f44,f79])).
% 2.10/0.70  fof(f44,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f20])).
% 2.10/0.70  fof(f20,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f19])).
% 2.10/0.70  fof(f19,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f9])).
% 2.10/0.70  fof(f9,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.10/0.70  fof(f1888,plain,(
% 2.10/0.70    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.10/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.10/0.70  fof(f1887,plain,(
% 2.10/0.70    spl5_17 | ~spl5_4 | ~spl5_10 | ~spl5_79 | ~spl5_167),
% 2.10/0.70    inference(avatar_split_clause,[],[f1886,f1565,f621,f104,f77,f160])).
% 2.10/0.70  fof(f104,plain,(
% 2.10/0.70    spl5_10 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.10/0.70  fof(f621,plain,(
% 2.10/0.70    spl5_79 <=> ! [X9,X8] : (r1_tarski(sK1,X8) | ~m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8)))))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 2.10/0.70  fof(f1565,plain,(
% 2.10/0.70    spl5_167 <=> ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).
% 2.10/0.70  fof(f1886,plain,(
% 2.10/0.70    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_4 | ~spl5_10 | ~spl5_79 | ~spl5_167)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f1883])).
% 2.10/0.70  fof(f1883,plain,(
% 2.10/0.70    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_4 | ~spl5_10 | ~spl5_79 | ~spl5_167)),
% 2.10/0.70    inference(resolution,[],[f1879,f54])).
% 2.10/0.70  fof(f54,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f27,plain,(
% 2.10/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f1])).
% 2.10/0.70  fof(f1,axiom,(
% 2.10/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.10/0.70  fof(f1879,plain,(
% 2.10/0.70    ( ! [X1] : (r2_hidden(sK4(sK1,X1),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X1)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79 | ~spl5_167)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f1871])).
% 2.10/0.70  fof(f1871,plain,(
% 2.10/0.70    ( ! [X1] : (r2_hidden(sK4(sK1,X1),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X1) | r1_tarski(sK1,X1)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79 | ~spl5_167)),
% 2.10/0.70    inference(resolution,[],[f1865,f1566])).
% 2.10/0.70  fof(f1566,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | ~spl5_167),
% 2.10/0.70    inference(avatar_component_clause,[],[f1565])).
% 2.10/0.70  fof(f1865,plain,(
% 2.10/0.70    ( ! [X4,X3] : (~r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X3))),X4) | r2_hidden(sK4(sK1,X3),X4) | r1_tarski(sK1,X3)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79)),
% 2.10/0.70    inference(resolution,[],[f1862,f52])).
% 2.10/0.70  fof(f52,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f1862,plain,(
% 2.10/0.70    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f1861])).
% 2.10/0.70  fof(f1861,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79)),
% 2.10/0.70    inference(resolution,[],[f1524,f279])).
% 2.10/0.70  fof(f279,plain,(
% 2.10/0.70    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)) ) | ~spl5_4),
% 2.10/0.70    inference(resolution,[],[f137,f79])).
% 2.10/0.70  fof(f137,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 2.10/0.70    inference(resolution,[],[f57,f53])).
% 2.10/0.70  fof(f53,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f57,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f29])).
% 2.10/0.70  fof(f29,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.10/0.70    inference(flattening,[],[f28])).
% 2.10/0.70  fof(f28,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.10/0.70    inference(ennf_transformation,[],[f5])).
% 2.10/0.70  fof(f5,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.10/0.70  fof(f1524,plain,(
% 2.10/0.70    ( ! [X0] : (~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0))))) ) | (~spl5_4 | ~spl5_10 | ~spl5_79)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f1523])).
% 2.10/0.70  fof(f1523,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_10 | ~spl5_79)),
% 2.10/0.70    inference(resolution,[],[f622,f576])).
% 2.10/0.70  fof(f576,plain,(
% 2.10/0.70    ( ! [X0] : (m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0)) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_10)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f575])).
% 2.10/0.70  fof(f575,plain,(
% 2.10/0.70    ( ! [X0] : (m1_connsp_2(sK3(sK4(sK1,X0)),sK0,sK4(sK1,X0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_10)),
% 2.10/0.70    inference(resolution,[],[f334,f53])).
% 2.10/0.70  fof(f334,plain,(
% 2.10/0.70    ( ! [X1] : (~r2_hidden(sK4(sK1,X1),sK1) | m1_connsp_2(sK3(sK4(sK1,X1)),sK0,sK4(sK1,X1)) | r1_tarski(sK1,X1)) ) | (~spl5_4 | ~spl5_10)),
% 2.10/0.70    inference(resolution,[],[f279,f105])).
% 2.10/0.70  fof(f105,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1)) ) | ~spl5_10),
% 2.10/0.70    inference(avatar_component_clause,[],[f104])).
% 2.10/0.70  fof(f622,plain,(
% 2.10/0.70    ( ! [X8,X9] : (~m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9) | r1_tarski(sK1,X8) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8))))) ) | ~spl5_79),
% 2.10/0.70    inference(avatar_component_clause,[],[f621])).
% 2.10/0.70  fof(f1567,plain,(
% 2.10/0.70    ~spl5_4 | spl5_167 | ~spl5_4 | ~spl5_9 | ~spl5_76),
% 2.10/0.70    inference(avatar_split_clause,[],[f1563,f609,f100,f77,f1565,f77])).
% 2.10/0.70  fof(f100,plain,(
% 2.10/0.70    spl5_9 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.10/0.70  fof(f609,plain,(
% 2.10/0.70    spl5_76 <=> ! [X3,X2] : (r1_tarski(sK1,X2) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3)) | ~r1_tarski(sK3(sK4(sK1,X2)),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 2.10/0.70  fof(f1563,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_4 | ~spl5_9 | ~spl5_76)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f1559])).
% 2.10/0.70  fof(f1559,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_9 | ~spl5_76)),
% 2.10/0.70    inference(resolution,[],[f610,f478])).
% 2.10/0.70  fof(f478,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(sK3(sK4(sK1,X0)),sK1) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_9)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f477])).
% 2.10/0.70  fof(f477,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(sK3(sK4(sK1,X0)),sK1) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_9)),
% 2.10/0.70    inference(resolution,[],[f335,f53])).
% 2.10/0.70  fof(f335,plain,(
% 2.10/0.70    ( ! [X2] : (~r2_hidden(sK4(sK1,X2),sK1) | r1_tarski(sK3(sK4(sK1,X2)),sK1) | r1_tarski(sK1,X2)) ) | (~spl5_4 | ~spl5_9)),
% 2.10/0.70    inference(resolution,[],[f279,f101])).
% 2.10/0.70  fof(f101,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl5_9),
% 2.10/0.70    inference(avatar_component_clause,[],[f100])).
% 2.10/0.70  fof(f610,plain,(
% 2.10/0.70    ( ! [X2,X3] : (~r1_tarski(sK3(sK4(sK1,X2)),X3) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3)) | r1_tarski(sK1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_76),
% 2.10/0.70    inference(avatar_component_clause,[],[f609])).
% 2.10/0.70  fof(f623,plain,(
% 2.10/0.70    spl5_3 | ~spl5_1 | ~spl5_2 | spl5_79 | ~spl5_4 | ~spl5_11),
% 2.10/0.70    inference(avatar_split_clause,[],[f598,f108,f77,f621,f67,f62,f72])).
% 2.10/0.70  fof(f72,plain,(
% 2.10/0.70    spl5_3 <=> v2_struct_0(sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.10/0.70  fof(f67,plain,(
% 2.10/0.70    spl5_2 <=> v2_pre_topc(sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.10/0.70  fof(f108,plain,(
% 2.10/0.70    spl5_11 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.10/0.70  fof(f598,plain,(
% 2.10/0.70    ( ! [X8,X9] : (r1_tarski(sK1,X8) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X9,k1_tops_1(sK0,sK3(sK4(sK1,X8)))) | ~m1_connsp_2(sK3(sK4(sK1,X8)),sK0,X9)) ) | (~spl5_4 | ~spl5_11)),
% 2.10/0.70    inference(resolution,[],[f515,f46])).
% 2.10/0.70  fof(f46,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f22])).
% 2.10/0.70  fof(f22,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.70    inference(flattening,[],[f21])).
% 2.10/0.70  fof(f21,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f10])).
% 2.10/0.70  fof(f10,axiom,(
% 2.10/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.10/0.70  fof(f515,plain,(
% 2.10/0.70    ( ! [X0] : (m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_11)),
% 2.10/0.70    inference(duplicate_literal_removal,[],[f514])).
% 2.10/0.70  fof(f514,plain,(
% 2.10/0.70    ( ! [X0] : (m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_11)),
% 2.10/0.70    inference(resolution,[],[f333,f53])).
% 2.10/0.70  fof(f333,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK1) | m1_subset_1(sK3(sK4(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | (~spl5_4 | ~spl5_11)),
% 2.10/0.70    inference(resolution,[],[f279,f109])).
% 2.10/0.70  fof(f109,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1)) ) | ~spl5_11),
% 2.10/0.70    inference(avatar_component_clause,[],[f108])).
% 2.10/0.70  fof(f611,plain,(
% 2.10/0.70    ~spl5_1 | spl5_76 | ~spl5_4 | ~spl5_11),
% 2.10/0.70    inference(avatar_split_clause,[],[f595,f108,f77,f609,f62])).
% 2.10/0.70  fof(f595,plain,(
% 2.10/0.70    ( ! [X2,X3] : (r1_tarski(sK1,X2) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3(sK4(sK1,X2)),X3) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X2))),k1_tops_1(sK0,X3))) ) | (~spl5_4 | ~spl5_11)),
% 2.10/0.70    inference(resolution,[],[f515,f43])).
% 2.10/0.70  fof(f43,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f18])).
% 2.10/0.70  fof(f18,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f17])).
% 2.10/0.70  fof(f17,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f8])).
% 2.10/0.70  fof(f8,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.10/0.70  fof(f239,plain,(
% 2.10/0.70    spl5_3 | spl5_29 | ~spl5_1 | ~spl5_2 | ~spl5_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f233,f77,f67,f62,f237,f72])).
% 2.10/0.70  fof(f233,plain,(
% 2.10/0.70    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X0)) ) | ~spl5_4),
% 2.10/0.70    inference(resolution,[],[f45,f79])).
% 2.10/0.70  fof(f45,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f22])).
% 2.10/0.70  fof(f176,plain,(
% 2.10/0.70    spl5_19 | ~spl5_2 | ~spl5_1 | ~spl5_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f170,f77,f62,f67,f173])).
% 2.10/0.70  fof(f173,plain,(
% 2.10/0.70    spl5_19 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.10/0.70  fof(f170,plain,(
% 2.10/0.70    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl5_4),
% 2.10/0.70    inference(resolution,[],[f48,f79])).
% 2.10/0.70  fof(f48,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f26])).
% 2.10/0.70  fof(f26,plain,(
% 2.10/0.70    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f25])).
% 2.10/0.70  fof(f25,plain,(
% 2.10/0.70    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f6])).
% 2.10/0.70  fof(f6,axiom,(
% 2.10/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.10/0.70  fof(f150,plain,(
% 2.10/0.70    spl5_15 | ~spl5_1 | ~spl5_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f144,f77,f62,f147])).
% 2.10/0.70  fof(f144,plain,(
% 2.10/0.70    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl5_4),
% 2.10/0.70    inference(resolution,[],[f42,f79])).
% 2.10/0.70  fof(f42,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f16])).
% 2.10/0.70  fof(f16,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f7])).
% 2.10/0.70  fof(f7,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.10/0.70  fof(f110,plain,(
% 2.10/0.70    spl5_5 | spl5_11),
% 2.10/0.70    inference(avatar_split_clause,[],[f32,f108,f82])).
% 2.10/0.70  fof(f32,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f15,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/0.70    inference(flattening,[],[f14])).
% 2.10/0.70  fof(f14,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f13])).
% 2.10/0.70  fof(f13,negated_conjecture,(
% 2.10/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.10/0.70    inference(negated_conjecture,[],[f12])).
% 2.10/0.70  fof(f12,conjecture,(
% 2.10/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 2.10/0.70  fof(f106,plain,(
% 2.10/0.70    spl5_5 | spl5_10),
% 2.10/0.70    inference(avatar_split_clause,[],[f33,f104,f82])).
% 2.10/0.70  fof(f33,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f102,plain,(
% 2.10/0.70    spl5_5 | spl5_9),
% 2.10/0.70    inference(avatar_split_clause,[],[f34,f100,f82])).
% 2.10/0.70  fof(f34,plain,(
% 2.10/0.70    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f98,plain,(
% 2.10/0.70    ~spl5_5 | spl5_8),
% 2.10/0.70    inference(avatar_split_clause,[],[f35,f96,f82])).
% 2.10/0.70  fof(f35,plain,(
% 2.10/0.70    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f94,plain,(
% 2.10/0.70    ~spl5_5 | spl5_7),
% 2.10/0.70    inference(avatar_split_clause,[],[f36,f91,f82])).
% 2.10/0.70  fof(f36,plain,(
% 2.10/0.70    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f89,plain,(
% 2.10/0.70    ~spl5_5 | spl5_6),
% 2.10/0.70    inference(avatar_split_clause,[],[f37,f86,f82])).
% 2.10/0.70  fof(f37,plain,(
% 2.10/0.70    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f80,plain,(
% 2.10/0.70    spl5_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f38,f77])).
% 2.10/0.70  fof(f38,plain,(
% 2.10/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f75,plain,(
% 2.10/0.70    ~spl5_3),
% 2.10/0.70    inference(avatar_split_clause,[],[f39,f72])).
% 2.10/0.70  fof(f39,plain,(
% 2.10/0.70    ~v2_struct_0(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f70,plain,(
% 2.10/0.70    spl5_2),
% 2.10/0.70    inference(avatar_split_clause,[],[f40,f67])).
% 2.10/0.70  fof(f40,plain,(
% 2.10/0.70    v2_pre_topc(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f65,plain,(
% 2.10/0.70    spl5_1),
% 2.10/0.70    inference(avatar_split_clause,[],[f41,f62])).
% 2.10/0.70  fof(f41,plain,(
% 2.10/0.70    l1_pre_topc(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  % SZS output end Proof for theBenchmark
% 2.10/0.70  % (24277)------------------------------
% 2.10/0.70  % (24277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.70  % (24277)Termination reason: Refutation
% 2.10/0.70  
% 2.10/0.70  % (24277)Memory used [KB]: 12409
% 2.10/0.70  % (24277)Time elapsed: 0.270 s
% 2.10/0.70  % (24277)------------------------------
% 2.10/0.70  % (24277)------------------------------
% 2.10/0.70  % (24260)Success in time 0.33 s
%------------------------------------------------------------------------------
