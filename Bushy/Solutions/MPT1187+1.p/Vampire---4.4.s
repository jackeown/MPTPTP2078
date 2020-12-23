%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t159_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 453 expanded)
%              Number of leaves         :   50 ( 192 expanded)
%              Depth                    :   10
%              Number of atoms          :  819 (1506 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f145,f149,f153,f157,f167,f171,f175,f189,f202,f210,f220,f227,f238,f259,f288,f316,f440,f450,f472,f523,f537,f572,f594,f605,f612,f677,f695,f713,f728,f841,f855])).

fof(f855,plain,
    ( ~ spl7_78
    | ~ spl7_94
    | ~ spl7_130 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | ~ spl7_78
    | ~ spl7_94
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f852,f471])).

fof(f471,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl7_78
  <=> m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f852,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_94
    | ~ spl7_130 ),
    inference(resolution,[],[f840,f604])).

fof(f604,plain,
    ( ! [X2] :
        ( ~ r2_orders_2(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl7_94
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f840,plain,
    ( r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f839])).

fof(f839,plain,
    ( spl7_130
  <=> r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f841,plain,
    ( spl7_130
    | ~ spl7_8
    | ~ spl7_12
    | spl7_71
    | ~ spl7_78
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f828,f570,f470,f438,f169,f155,f839])).

fof(f155,plain,
    ( spl7_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f169,plain,
    ( spl7_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f438,plain,
    ( spl7_71
  <=> sK1 != sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f570,plain,
    ( spl7_90
  <=> r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f828,plain,
    ( r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_71
    | ~ spl7_78
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f827,f439])).

fof(f439,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f438])).

fof(f827,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_78
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f826,f156])).

fof(f156,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f826,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_12
    | ~ spl7_78
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f825,f471])).

fof(f825,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_12
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f819,f170])).

fof(f170,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f819,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | r2_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_90 ),
    inference(resolution,[],[f571,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',d10_orders_2)).

fof(f571,plain,
    ( r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f570])).

fof(f728,plain,
    ( ~ spl7_8
    | ~ spl7_12
    | ~ spl7_108 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_108 ),
    inference(subsumption_resolution,[],[f726,f170])).

fof(f726,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_8
    | ~ spl7_108 ),
    inference(subsumption_resolution,[],[f720,f156])).

fof(f720,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_108 ),
    inference(resolution,[],[f712,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(condensation,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',irreflexivity_r2_orders_2)).

fof(f712,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl7_108
  <=> r2_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f713,plain,
    ( spl7_108
    | ~ spl7_92
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f700,f693,f592,f711])).

fof(f592,plain,
    ( spl7_92
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f693,plain,
    ( spl7_104
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f700,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl7_92
    | ~ spl7_104 ),
    inference(superposition,[],[f593,f694])).

fof(f694,plain,
    ( sK1 = sK2
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f693])).

fof(f593,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f592])).

fof(f695,plain,
    ( spl7_104
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_42
    | ~ spl7_86
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f688,f675,f535,f286,f257,f600,f693])).

fof(f600,plain,
    ( spl7_16
  <=> r6_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f257,plain,
    ( spl7_34
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f286,plain,
    ( spl7_42
  <=> u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f535,plain,
    ( spl7_86
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f675,plain,
    ( spl7_102
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f688,plain,
    ( sK1 = sK2
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_42
    | ~ spl7_86
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f687,f536])).

fof(f536,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f535])).

fof(f687,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_42
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f686,f287])).

fof(f287,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f286])).

fof(f686,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | sK1 = sK2
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f685,f601])).

fof(f601,plain,
    ( r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f600])).

fof(f685,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | sK1 = sK2
    | ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_34
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f679,f258])).

fof(f258,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f257])).

fof(f679,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | sK1 = sK2
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_102 ),
    inference(resolution,[],[f676,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | ~ v1_relat_1(X0)
      | ~ r6_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ~ ( r2_hidden(k4_tarski(X1,X2),X0)
                  & X1 != X2
                  & r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',d11_orders_1)).

fof(f676,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f675])).

fof(f677,plain,
    ( spl7_102
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f618,f610,f187,f169,f155,f675])).

fof(f187,plain,
    ( spl7_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f610,plain,
    ( spl7_96
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f618,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f617,f156])).

fof(f617,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f616,f188])).

fof(f188,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f616,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_12
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f613,f170])).

fof(f613,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_96 ),
    inference(resolution,[],[f611,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',d9_orders_2)).

fof(f611,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f610])).

fof(f612,plain,
    ( spl7_96
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f598,f592,f187,f169,f155,f610])).

fof(f598,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_92 ),
    inference(subsumption_resolution,[],[f597,f156])).

fof(f597,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_92 ),
    inference(subsumption_resolution,[],[f596,f188])).

fof(f596,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl7_12
    | ~ spl7_92 ),
    inference(subsumption_resolution,[],[f595,f170])).

fof(f595,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl7_92 ),
    inference(resolution,[],[f593,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f605,plain,
    ( spl7_16
    | spl7_94 ),
    inference(avatar_split_clause,[],[f91,f603,f600])).

fof(f91,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X2)
      | r6_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r6_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r6_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',t159_orders_2)).

fof(f594,plain,
    ( ~ spl7_17
    | spl7_92 ),
    inference(avatar_split_clause,[],[f90,f592,f184])).

fof(f184,plain,
    ( spl7_17
  <=> ~ r6_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f90,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r6_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f572,plain,
    ( spl7_90
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_78
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f560,f521,f470,f169,f155,f570])).

fof(f521,plain,
    ( spl7_84
  <=> r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f560,plain,
    ( r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_78
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f559,f156])).

fof(f559,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_12
    | ~ spl7_78
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f558,f471])).

fof(f558,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_12
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f551,f170])).

fof(f551,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl7_84 ),
    inference(resolution,[],[f522,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f522,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f521])).

fof(f537,plain,
    ( spl7_86
    | ~ spl7_18
    | spl7_31 ),
    inference(avatar_split_clause,[],[f485,f240,f187,f535])).

fof(f240,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f485,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_18
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f477,f241])).

fof(f241,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f240])).

fof(f477,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(resolution,[],[f188,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',t2_subset)).

fof(f523,plain,
    ( spl7_84
    | spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f492,f286,f257,f222,f184,f521])).

fof(f222,plain,
    ( spl7_28
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f492,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f460,f185])).

fof(f185,plain,
    ( ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f460,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(resolution,[],[f295,f223])).

fof(f223,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f222])).

fof(f295,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X2,sK3(u1_orders_2(sK0),X2)),u1_orders_2(sK0))
        | r6_orders_1(u1_orders_2(sK0),X2) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f291,f258])).

fof(f291,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0))
        | r2_hidden(k4_tarski(X2,sK3(u1_orders_2(sK0),X2)),u1_orders_2(sK0))
        | r6_orders_1(u1_orders_2(sK0),X2) )
    | ~ spl7_42 ),
    inference(superposition,[],[f104,f287])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
      | r6_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f472,plain,
    ( spl7_78
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f456,f448,f470])).

fof(f448,plain,
    ( spl7_74
  <=> r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f456,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_74 ),
    inference(resolution,[],[f449,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',t1_subset)).

fof(f449,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f448])).

fof(f450,plain,
    ( spl7_74
    | spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f442,f286,f257,f222,f184,f448])).

fof(f442,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f441,f185])).

fof(f441,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(resolution,[],[f293,f223])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | r6_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(forward_demodulation,[],[f292,f287])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | r6_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f289,f258])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | r6_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl7_42 ),
    inference(superposition,[],[f102,f287])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | r6_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f440,plain,
    ( ~ spl7_71
    | spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f436,f286,f257,f222,f184,f438])).

fof(f436,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | ~ spl7_17
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f435,f185])).

fof(f435,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl7_28
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(resolution,[],[f294,f223])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | sK3(u1_orders_2(sK0),X1) != X1
        | r6_orders_1(u1_orders_2(sK0),X1) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f290,f258])).

fof(f290,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0))
        | sK3(u1_orders_2(sK0),X1) != X1
        | r6_orders_1(u1_orders_2(sK0),X1) )
    | ~ spl7_42 ),
    inference(superposition,[],[f103,f287])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | sK3(X0,X1) != X1
      | r6_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f316,plain,
    ( spl7_1
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f314,f140])).

fof(f140,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f314,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f312,f166])).

fof(f166,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl7_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f312,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30 ),
    inference(resolution,[],[f226,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',fc2_struct_0)).

fof(f226,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_30
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f288,plain,
    ( spl7_42
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f251,f236,f218,f208,f200,f173,f155,f286])).

fof(f173,plain,
    ( spl7_14
  <=> v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f200,plain,
    ( spl7_20
  <=> v1_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f208,plain,
    ( spl7_24
  <=> v8_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f218,plain,
    ( spl7_26
  <=> v4_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f236,plain,
    ( spl7_32
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f251,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f250,f201])).

fof(f201,plain,
    ( v1_relat_2(u1_orders_2(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f250,plain,
    ( ~ v1_relat_2(u1_orders_2(sK0))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f249,f194])).

fof(f194,plain,
    ( v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f191,f156])).

fof(f191,plain,
    ( ~ l1_orders_2(sK0)
    | v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f174,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',fc2_orders_2)).

fof(f174,plain,
    ( v2_orders_2(sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f249,plain,
    ( ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f248,f209])).

fof(f209,plain,
    ( v8_relat_2(u1_orders_2(sK0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f248,plain,
    ( ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_26
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f243,f219])).

fof(f219,plain,
    ( v4_relat_2(u1_orders_2(sK0))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f243,plain,
    ( ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl7_32 ),
    inference(resolution,[],[f237,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v4_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_relat_2(X1)
      | k3_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',t100_orders_1)).

fof(f237,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f236])).

fof(f259,plain,
    ( spl7_34
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f244,f236,f257])).

fof(f244,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl7_32 ),
    inference(resolution,[],[f237,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',cc1_relset_1)).

fof(f238,plain,
    ( spl7_32
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f161,f155,f236])).

fof(f161,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_8 ),
    inference(resolution,[],[f156,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',dt_u1_orders_2)).

fof(f227,plain,
    ( spl7_28
    | spl7_30
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f178,f169,f225,f222])).

fof(f178,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_12 ),
    inference(resolution,[],[f170,f124])).

fof(f220,plain,
    ( spl7_26
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f198,f173,f155,f151,f218])).

fof(f151,plain,
    ( spl7_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f198,plain,
    ( v4_relat_2(u1_orders_2(sK0))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f197,f156])).

fof(f197,plain,
    ( ~ l1_orders_2(sK0)
    | v4_relat_2(u1_orders_2(sK0))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f193,f152])).

fof(f152,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f193,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_relat_2(u1_orders_2(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f174,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',fc4_orders_2)).

fof(f210,plain,
    ( spl7_24
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f196,f173,f155,f147,f208])).

fof(f147,plain,
    ( spl7_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f196,plain,
    ( v8_relat_2(u1_orders_2(sK0))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f195,f156])).

fof(f195,plain,
    ( ~ l1_orders_2(sK0)
    | v8_relat_2(u1_orders_2(sK0))
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f192,f148])).

fof(f148,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f192,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v8_relat_2(u1_orders_2(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f174,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v2_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v8_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',fc5_orders_2)).

fof(f202,plain,
    ( spl7_20
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f162,f155,f143,f200])).

fof(f143,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f162,plain,
    ( v1_relat_2(u1_orders_2(sK0))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f158,f144])).

fof(f144,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f158,plain,
    ( ~ v3_orders_2(sK0)
    | v1_relat_2(u1_orders_2(sK0))
    | ~ spl7_8 ),
    inference(resolution,[],[f156,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v1_relat_2(u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',fc3_orders_2)).

fof(f189,plain,
    ( ~ spl7_17
    | spl7_18 ),
    inference(avatar_split_clause,[],[f89,f187,f184])).

fof(f89,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r6_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f175,plain,
    ( spl7_14
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f163,f155,f143,f173])).

fof(f163,plain,
    ( v2_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f160,f144])).

fof(f160,plain,
    ( ~ v3_orders_2(sK0)
    | v2_orders_2(sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f156,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',cc1_orders_2)).

fof(f171,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f92,f169])).

fof(f92,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f167,plain,
    ( spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f159,f155,f165])).

fof(f159,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f156,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t159_orders_2.p',dt_l1_orders_2)).

fof(f157,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f97,f155])).

fof(f97,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f153,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f96,f151])).

fof(f96,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f149,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f95,f147])).

fof(f95,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f145,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f94,f143])).

fof(f94,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f141,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f93,f139])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
