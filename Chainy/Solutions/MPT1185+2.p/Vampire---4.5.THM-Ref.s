%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1185+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 28.32s
% Output     : Refutation 28.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 198 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  348 ( 644 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4927,f4931,f4935,f4970,f4978,f4990,f5227,f5231,f5321,f5341,f7182,f7494,f8648,f8662,f21385])).

fof(f21385,plain,
    ( spl328_8
    | ~ spl328_11
    | ~ spl328_16
    | ~ spl328_17
    | ~ spl328_53
    | ~ spl328_60
    | ~ spl328_78
    | ~ spl328_79 ),
    inference(avatar_contradiction_clause,[],[f21384])).

fof(f21384,plain,
    ( $false
    | spl328_8
    | ~ spl328_11
    | ~ spl328_16
    | ~ spl328_17
    | ~ spl328_53
    | ~ spl328_60
    | ~ spl328_78
    | ~ spl328_79 ),
    inference(subsumption_resolution,[],[f21372,f21360])).

fof(f21360,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | spl328_8
    | ~ spl328_11
    | ~ spl328_16
    | ~ spl328_53
    | ~ spl328_60
    | ~ spl328_78
    | ~ spl328_79 ),
    inference(subsumption_resolution,[],[f8780,f21348])).

fof(f21348,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_11
    | ~ spl328_16
    | ~ spl328_53 ),
    inference(resolution,[],[f7471,f5226])).

fof(f5226,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl328_11 ),
    inference(avatar_component_clause,[],[f5225])).

fof(f5225,plain,
    ( spl328_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_11])])).

fof(f7471,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r8_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl328_16
    | ~ spl328_53 ),
    inference(subsumption_resolution,[],[f5368,f7380])).

fof(f7380,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl328_53 ),
    inference(resolution,[],[f7181,f3129])).

fof(f3129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2049])).

fof(f2049,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f7181,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl328_53 ),
    inference(avatar_component_clause,[],[f7180])).

fof(f7180,plain,
    ( spl328_53
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_53])])).

fof(f5368,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(u1_orders_2(sK0))
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | r8_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl328_16 ),
    inference(resolution,[],[f5320,f3222])).

fof(f3222,plain,(
    ! [X2,X0,X1] :
      ( ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r8_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f2096])).

fof(f2096,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2095])).

fof(f2095,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1980])).

fof(f1980,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

fof(f5320,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl328_16 ),
    inference(avatar_component_clause,[],[f5319])).

fof(f5319,plain,
    ( spl328_16
  <=> r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_16])])).

fof(f8780,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | spl328_8
    | ~ spl328_60
    | ~ spl328_78
    | ~ spl328_79 ),
    inference(subsumption_resolution,[],[f8779,f4977])).

fof(f4977,plain,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
    | spl328_8 ),
    inference(avatar_component_clause,[],[f4976])).

fof(f4976,plain,
    ( spl328_8
  <=> r3_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_8])])).

fof(f8779,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl328_60
    | ~ spl328_78
    | ~ spl328_79 ),
    inference(subsumption_resolution,[],[f8778,f8661])).

fof(f8661,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_79 ),
    inference(avatar_component_clause,[],[f8660])).

fof(f8660,plain,
    ( spl328_79
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_79])])).

fof(f8778,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r6_relat_2(u1_orders_2(sK0),sK1)
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl328_60
    | ~ spl328_78 ),
    inference(subsumption_resolution,[],[f8776,f7493])).

fof(f7493,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl328_60 ),
    inference(avatar_component_clause,[],[f7492])).

fof(f7492,plain,
    ( spl328_60
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_60])])).

fof(f8776,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r6_relat_2(u1_orders_2(sK0),sK1)
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl328_78 ),
    inference(resolution,[],[f8647,f3108])).

fof(f3108,plain,(
    ! [X0,X1] :
      ( ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r8_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | r3_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2030])).

fof(f2030,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f1879,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

fof(f8647,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_78 ),
    inference(avatar_component_clause,[],[f8646])).

fof(f8646,plain,
    ( spl328_78
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_78])])).

fof(f21372,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_11
    | ~ spl328_17
    | ~ spl328_53 ),
    inference(resolution,[],[f7472,f5226])).

fof(f7472,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r4_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl328_17
    | ~ spl328_53 ),
    inference(subsumption_resolution,[],[f5370,f7380])).

fof(f5370,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(u1_orders_2(sK0))
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | r4_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl328_17 ),
    inference(resolution,[],[f5340,f3210])).

fof(f3210,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r4_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f2090])).

fof(f2090,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2089])).

fof(f2089,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1979])).

fof(f1979,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

fof(f5340,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl328_17 ),
    inference(avatar_component_clause,[],[f5339])).

fof(f5339,plain,
    ( spl328_17
  <=> r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_17])])).

fof(f8662,plain,
    ( spl328_79
    | ~ spl328_12
    | ~ spl328_53 ),
    inference(avatar_split_clause,[],[f7467,f7180,f5229,f8660])).

fof(f5229,plain,
    ( spl328_12
  <=> r7_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_12])])).

fof(f7467,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_12
    | ~ spl328_53 ),
    inference(subsumption_resolution,[],[f5305,f7380])).

fof(f5305,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl328_12 ),
    inference(resolution,[],[f5230,f3194])).

fof(f3194,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r6_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2085])).

fof(f2085,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1977])).

fof(f1977,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(f5230,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_12 ),
    inference(avatar_component_clause,[],[f5229])).

fof(f8648,plain,
    ( spl328_78
    | ~ spl328_12
    | ~ spl328_53 ),
    inference(avatar_split_clause,[],[f7466,f7180,f5229,f8646])).

fof(f7466,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_12
    | ~ spl328_53 ),
    inference(subsumption_resolution,[],[f5304,f7380])).

fof(f5304,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl328_12 ),
    inference(resolution,[],[f5230,f3193])).

fof(f3193,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2085])).

fof(f7494,plain,
    ( spl328_60
    | ~ spl328_53 ),
    inference(avatar_split_clause,[],[f7380,f7180,f7492])).

fof(f7182,plain,
    ( spl328_53
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4966,f4933,f7180])).

fof(f4933,plain,
    ( spl328_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_5])])).

fof(f4966,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl328_5 ),
    inference(resolution,[],[f4934,f3125])).

fof(f3125,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f2042])).

fof(f2042,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1897])).

fof(f1897,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f4934,plain,
    ( l1_orders_2(sK0)
    | ~ spl328_5 ),
    inference(avatar_component_clause,[],[f4933])).

fof(f5341,plain,
    ( spl328_17
    | ~ spl328_4
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4963,f4933,f4929,f5339])).

fof(f4929,plain,
    ( spl328_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_4])])).

fof(f4963,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl328_4
    | ~ spl328_5 ),
    inference(subsumption_resolution,[],[f4946,f4934])).

fof(f4946,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl328_4 ),
    inference(resolution,[],[f4930,f3220])).

fof(f3220,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2094])).

fof(f2094,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1877])).

fof(f1877,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f4930,plain,
    ( v5_orders_2(sK0)
    | ~ spl328_4 ),
    inference(avatar_component_clause,[],[f4929])).

fof(f5321,plain,
    ( spl328_16
    | ~ spl328_3
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4941,f4933,f4925,f5319])).

fof(f4925,plain,
    ( spl328_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_3])])).

fof(f4941,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl328_3
    | ~ spl328_5 ),
    inference(subsumption_resolution,[],[f4940,f4934])).

fof(f4940,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl328_3 ),
    inference(resolution,[],[f4926,f3233])).

fof(f3233,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2100,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1876])).

fof(f1876,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(f4926,plain,
    ( v4_orders_2(sK0)
    | ~ spl328_3 ),
    inference(avatar_component_clause,[],[f4925])).

fof(f5231,plain,
    ( spl328_12
    | ~ spl328_5
    | ~ spl328_6
    | ~ spl328_10 ),
    inference(avatar_split_clause,[],[f5208,f4988,f4968,f4933,f5229])).

fof(f4968,plain,
    ( spl328_6
  <=> v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_6])])).

fof(f4988,plain,
    ( spl328_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_10])])).

fof(f5208,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl328_5
    | ~ spl328_6
    | ~ spl328_10 ),
    inference(subsumption_resolution,[],[f5207,f4969])).

fof(f4969,plain,
    ( v6_orders_2(sK1,sK0)
    | ~ spl328_6 ),
    inference(avatar_component_clause,[],[f4968])).

fof(f5207,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0)
    | ~ spl328_5
    | ~ spl328_10 ),
    inference(subsumption_resolution,[],[f5024,f4934])).

fof(f5024,plain,
    ( ~ l1_orders_2(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0)
    | ~ spl328_10 ),
    inference(resolution,[],[f4989,f3859])).

fof(f3859,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2476])).

fof(f2476,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1864])).

fof(f1864,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f4989,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl328_10 ),
    inference(avatar_component_clause,[],[f4988])).

fof(f5227,plain,
    ( spl328_11
    | ~ spl328_10 ),
    inference(avatar_split_clause,[],[f5027,f4988,f5225])).

fof(f5027,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl328_10 ),
    inference(resolution,[],[f4989,f3131])).

fof(f3131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f4990,plain,(
    spl328_10 ),
    inference(avatar_split_clause,[],[f3096,f4988])).

fof(f3096,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2027])).

fof(f2027,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2026])).

fof(f2026,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1928])).

fof(f1928,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1927])).

fof(f1927,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).

fof(f4978,plain,(
    ~ spl328_8 ),
    inference(avatar_split_clause,[],[f3097,f4976])).

fof(f3097,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f2027])).

fof(f4970,plain,(
    spl328_6 ),
    inference(avatar_split_clause,[],[f3095,f4968])).

fof(f3095,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f2027])).

fof(f4935,plain,(
    spl328_5 ),
    inference(avatar_split_clause,[],[f3102,f4933])).

fof(f3102,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2027])).

fof(f4931,plain,(
    spl328_4 ),
    inference(avatar_split_clause,[],[f3101,f4929])).

fof(f3101,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2027])).

fof(f4927,plain,(
    spl328_3 ),
    inference(avatar_split_clause,[],[f3100,f4925])).

fof(f3100,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2027])).
%------------------------------------------------------------------------------
