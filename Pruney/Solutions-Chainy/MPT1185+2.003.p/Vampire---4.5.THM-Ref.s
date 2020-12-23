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
% DateTime   : Thu Dec  3 13:10:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 467 expanded)
%              Number of leaves         :   19 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  310 (1888 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f192,f196,f212])).

fof(f212,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f210,f198])).

fof(f198,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f173,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r4_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f143,f120])).

fof(f120,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f118,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f116,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r4_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f65,f106])).

fof(f106,plain,(
    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f105,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r4_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).

fof(f173,plain,
    ( ! [X4] : r1_tarski(sK1,X4)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_12
  <=> ! [X4] : r1_tarski(sK1,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f210,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f194,f197])).

fof(f197,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f173,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r8_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f146,f120])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r8_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f66,f109])).

fof(f109,plain,(
    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f108,f43])).

fof(f108,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r8_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).

fof(f194,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f193,f38])).

fof(f38,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f193,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f187,f120])).

fof(f187,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f186,f181])).

fof(f181,plain,(
    r1_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f179,f120])).

fof(f179,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f177,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(f177,plain,(
    r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f176,f36])).

fof(f36,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f176,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f175,f43])).

fof(f175,plain,
    ( ~ l1_orders_2(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f186,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f56,f180])).

fof(f180,plain,(
    r6_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f178,f120])).

fof(f178,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f177,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r6_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0)
      | r3_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

fof(f196,plain,
    ( spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f195,f97,f172])).

fof(f97,plain,
    ( spl4_5
  <=> sP3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f195,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f99,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP3(X1) ) ),
    inference(general_splitting,[],[f68,f69_D])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP3(X1) ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP3(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f99,plain,
    ( sP3(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f192,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f190,f38])).

fof(f190,plain,
    ( r3_orders_1(u1_orders_2(sK0),sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f189,f120])).

fof(f189,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f188,f161])).

fof(f161,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | spl4_6 ),
    inference(resolution,[],[f159,f144])).

fof(f159,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | spl4_6 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0))
    | spl4_6 ),
    inference(resolution,[],[f154,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) )
    | spl4_6 ),
    inference(subsumption_resolution,[],[f153,f103])).

fof(f103,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(sK2(sK1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f151,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f151,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f114,f37])).

fof(f114,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(sK2(X1,X3),X2)
      | r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f67,f63])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f188,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f187,f160])).

fof(f160,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | spl4_6 ),
    inference(resolution,[],[f159,f147])).

fof(f104,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f95,f101,f97])).

fof(f95,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP3(sK1) ),
    inference(resolution,[],[f69,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (23188)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (23193)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (23193)Refutation not found, incomplete strategy% (23193)------------------------------
% 0.22/0.47  % (23193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23193)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23193)Memory used [KB]: 9850
% 0.22/0.47  % (23193)Time elapsed: 0.051 s
% 0.22/0.47  % (23193)------------------------------
% 0.22/0.47  % (23193)------------------------------
% 0.22/0.48  % (23202)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (23187)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.51  % (23198)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.51  % (23198)Refutation not found, incomplete strategy% (23198)------------------------------
% 0.22/0.51  % (23198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23198)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23198)Memory used [KB]: 5373
% 0.22/0.51  % (23198)Time elapsed: 0.004 s
% 0.22/0.51  % (23198)------------------------------
% 0.22/0.51  % (23198)------------------------------
% 0.22/0.51  % (23187)Refutation not found, incomplete strategy% (23187)------------------------------
% 0.22/0.51  % (23187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23187)Memory used [KB]: 9850
% 0.22/0.51  % (23187)Time elapsed: 0.072 s
% 0.22/0.51  % (23187)------------------------------
% 0.22/0.51  % (23187)------------------------------
% 0.22/0.52  % (23191)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.52  % (23190)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.52  % (23197)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (23194)WARNING: option uwaf not known.
% 0.22/0.52  % (23192)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (23190)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f104,f192,f196,f212])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    ~spl4_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    $false | ~spl4_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f210,f198])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    r4_relat_2(u1_orders_2(sK0),sK1) | ~spl4_12),
% 0.22/0.52    inference(resolution,[],[f173,f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r4_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.52    inference(resolution,[],[f116,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.52    inference(resolution,[],[f44,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f15])).
% 0.22/0.52  fof(f15,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r1_tarski(X0,u1_struct_0(sK0)) | r4_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.52    inference(resolution,[],[f65,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f105,f43])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.52    inference(resolution,[],[f46,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (~v5_orders_2(X0) | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r4_relat_2(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | r4_relat_2(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r4_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r4_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r4_relat_2(X2,X0)) => r4_relat_2(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ( ! [X4] : (r1_tarski(sK1,X4)) ) | ~spl4_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f172])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    spl4_12 <=> ! [X4] : r1_tarski(sK1,X4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    ~r4_relat_2(u1_orders_2(sK0),sK1) | ~spl4_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f194,f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    r8_relat_2(u1_orders_2(sK0),sK1) | ~spl4_12),
% 0.22/0.52    inference(resolution,[],[f173,f147])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r8_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f146,f120])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r1_tarski(X0,u1_struct_0(sK0)) | r8_relat_2(u1_orders_2(sK0),X0)) )),
% 0.22/0.52    inference(resolution,[],[f66,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f43])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.52    inference(resolution,[],[f48,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~v4_orders_2(X0) | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r8_relat_2(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | r8_relat_2(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r8_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r8_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r8_relat_2(X2,X0)) => r8_relat_2(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f193,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f120])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f186,f181])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f179,f120])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.52    inference(resolution,[],[f177,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r1_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f176,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    v6_orders_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f43])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ~l1_orders_2(sK0) | r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f50,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    ~r1_relat_2(u1_orders_2(sK0),sK1) | ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(resolution,[],[f56,f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f120])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    r6_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.52    inference(resolution,[],[f177,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r6_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r6_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~v1_relat_1(X0) | r3_orders_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    spl4_12 | ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f195,f97,f172])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl4_5 <=> sP3(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_5),
% 0.22/0.52    inference(resolution,[],[f99,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP3(X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f63,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP3(X1)) )),
% 0.22/0.52    inference(general_splitting,[],[f68,f69_D])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP3(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f69_D])).
% 0.22/0.52  fof(f69_D,plain,(
% 0.22/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP3(X1)) )),
% 0.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    sP3(sK1) | ~spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    spl4_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    $false | spl4_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f38])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    r3_orders_1(u1_orders_2(sK0),sK1) | spl4_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f189,f120])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1) | spl4_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f188,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    r4_relat_2(u1_orders_2(sK0),sK1) | spl4_6),
% 0.22/0.52    inference(resolution,[],[f159,f144])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | spl4_6),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f155])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,u1_struct_0(sK0)) | spl4_6),
% 0.22/0.52    inference(resolution,[],[f154,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK2(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)) ) | spl4_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl4_6 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(sK1,X0) | v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2(sK1,X0),u1_struct_0(sK0))) )),
% 0.22/0.52    inference(resolution,[],[f151,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f114,f37])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(sK2(X1,X3),X2) | r1_tarski(X1,X3)) )),
% 0.22/0.52    inference(resolution,[],[f67,f63])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1) | spl4_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f160])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    r8_relat_2(u1_orders_2(sK0),sK1) | spl4_6),
% 0.22/0.52    inference(resolution,[],[f159,f147])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    spl4_5 | ~spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f95,f101,f97])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | sP3(sK1)),
% 0.22/0.52    inference(resolution,[],[f69,f37])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23190)------------------------------
% 0.22/0.52  % (23190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23190)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23190)Memory used [KB]: 5373
% 0.22/0.52  % (23190)Time elapsed: 0.032 s
% 0.22/0.52  % (23190)------------------------------
% 0.22/0.52  % (23190)------------------------------
% 0.22/0.52  % (23194)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 1.35/0.53  % (23183)Success in time 0.167 s
%------------------------------------------------------------------------------
