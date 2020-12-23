%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t160_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 4.21s
% Output     : Refutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  258 ( 514 expanded)
%              Number of leaves         :   55 ( 190 expanded)
%              Depth                    :   15
%              Number of atoms          : 1059 (2926 expanded)
%              Number of equality atoms :   90 ( 355 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f189,f196,f203,f210,f238,f281,f366,f382,f422,f486,f505,f541,f550,f710,f732,f2921,f3280,f23750,f24089,f24431,f24593,f38572,f38613,f38997,f39174,f39195,f39362,f39385,f40150,f75457])).

fof(f75457,plain,
    ( ~ spl10_8
    | ~ spl10_68
    | ~ spl10_1344
    | ~ spl10_1374
    | spl10_1377 ),
    inference(avatar_contradiction_clause,[],[f75456])).

fof(f75456,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_68
    | ~ spl10_1344
    | ~ spl10_1374
    | ~ spl10_1377 ),
    inference(subsumption_resolution,[],[f75455,f24070])).

fof(f24070,plain,
    ( v2_orders_2(sK0)
    | ~ spl10_1374 ),
    inference(avatar_component_clause,[],[f24069])).

fof(f24069,plain,
    ( spl10_1374
  <=> v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1374])])).

fof(f75455,plain,
    ( ~ v2_orders_2(sK0)
    | ~ spl10_8
    | ~ spl10_68
    | ~ spl10_1344
    | ~ spl10_1377 ),
    inference(subsumption_resolution,[],[f75454,f209])).

fof(f209,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl10_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f75454,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0)
    | ~ spl10_68
    | ~ spl10_1344
    | ~ spl10_1377 ),
    inference(subsumption_resolution,[],[f75453,f24076])).

fof(f24076,plain,
    ( u1_struct_0(sK0) != k3_relat_1(u1_orders_2(sK0))
    | ~ spl10_1377 ),
    inference(avatar_component_clause,[],[f24075])).

fof(f24075,plain,
    ( spl10_1377
  <=> u1_struct_0(sK0) != k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1377])])).

fof(f75453,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0)
    | ~ spl10_68
    | ~ spl10_1344 ),
    inference(subsumption_resolution,[],[f75452,f485])).

fof(f485,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl10_68
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f75452,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0)
    | ~ spl10_1344 ),
    inference(resolution,[],[f23749,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',fc2_orders_2)).

fof(f23749,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(u1_orders_2(sK0),X0)
        | ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k3_relat_1(u1_orders_2(sK0)) = X0 )
    | ~ spl10_1344 ),
    inference(avatar_component_clause,[],[f23748])).

fof(f23748,plain,
    ( spl10_1344
  <=> ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1344])])).

fof(f40150,plain,
    ( spl10_27
    | ~ spl10_56
    | spl10_1383
    | ~ spl10_1402 ),
    inference(avatar_contradiction_clause,[],[f40149])).

fof(f40149,plain,
    ( $false
    | ~ spl10_27
    | ~ spl10_56
    | ~ spl10_1383
    | ~ spl10_1402 ),
    inference(unit_resulting_resolution,[],[f415,f274,f24287,f24592])).

fof(f24592,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0)
        | m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0)) )
    | ~ spl10_1402 ),
    inference(avatar_component_clause,[],[f24591])).

fof(f24591,plain,
    ( spl10_1402
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0)
        | m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1402])])).

fof(f24287,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_1383 ),
    inference(avatar_component_clause,[],[f24286])).

fof(f24286,plain,
    ( spl10_1383
  <=> ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1383])])).

fof(f274,plain,
    ( ~ r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl10_27
  <=> ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f415,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl10_56
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f39385,plain,
    ( ~ spl10_8
    | ~ spl10_16
    | spl10_29
    | ~ spl10_50
    | spl10_331
    | ~ spl10_2122 ),
    inference(avatar_contradiction_clause,[],[f39384])).

fof(f39384,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_29
    | ~ spl10_50
    | ~ spl10_331
    | ~ spl10_2122 ),
    inference(subsumption_resolution,[],[f39383,f209])).

fof(f39383,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_16
    | ~ spl10_29
    | ~ spl10_50
    | ~ spl10_331
    | ~ spl10_2122 ),
    inference(subsumption_resolution,[],[f39382,f381])).

fof(f381,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl10_50
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f39382,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_16
    | ~ spl10_29
    | ~ spl10_331
    | ~ spl10_2122 ),
    inference(subsumption_resolution,[],[f39381,f237])).

fof(f237,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl10_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f39381,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_29
    | ~ spl10_331
    | ~ spl10_2122 ),
    inference(subsumption_resolution,[],[f39380,f3279])).

fof(f3279,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ spl10_331 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f3278,plain,
    ( spl10_331
  <=> ~ r2_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_331])])).

fof(f39380,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_29
    | ~ spl10_2122 ),
    inference(subsumption_resolution,[],[f39377,f280])).

fof(f280,plain,
    ( sK1 != sK2
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl10_29
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f39377,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_2122 ),
    inference(resolution,[],[f39361,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',d10_orders_2)).

fof(f39361,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl10_2122 ),
    inference(avatar_component_clause,[],[f39360])).

fof(f39360,plain,
    ( spl10_2122
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2122])])).

fof(f39362,plain,
    ( spl10_2122
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_50
    | ~ spl10_2120 ),
    inference(avatar_split_clause,[],[f39355,f39179,f380,f236,f208,f39360])).

fof(f39179,plain,
    ( spl10_2120
  <=> r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2120])])).

fof(f39355,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_50
    | ~ spl10_2120 ),
    inference(subsumption_resolution,[],[f39354,f209])).

fof(f39354,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_16
    | ~ spl10_50
    | ~ spl10_2120 ),
    inference(subsumption_resolution,[],[f39353,f381])).

fof(f39353,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_16
    | ~ spl10_2120 ),
    inference(subsumption_resolution,[],[f39347,f237])).

fof(f39347,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_2120 ),
    inference(resolution,[],[f39180,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',d9_orders_2)).

fof(f39180,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl10_2120 ),
    inference(avatar_component_clause,[],[f39179])).

fof(f39195,plain,
    ( spl10_2120
    | spl10_29
    | ~ spl10_104
    | ~ spl10_2118 ),
    inference(avatar_split_clause,[],[f39189,f39167,f730,f279,f39179])).

fof(f730,plain,
    ( spl10_104
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f39167,plain,
    ( spl10_2118
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2118])])).

fof(f39189,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl10_29
    | ~ spl10_104
    | ~ spl10_2118 ),
    inference(subsumption_resolution,[],[f39183,f280])).

fof(f39183,plain,
    ( sK1 = sK2
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl10_104
    | ~ spl10_2118 ),
    inference(resolution,[],[f39168,f731])).

fof(f731,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f730])).

fof(f39168,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) )
    | ~ spl10_2118 ),
    inference(avatar_component_clause,[],[f39167])).

fof(f39174,plain,
    ( spl10_2118
    | ~ spl10_26
    | ~ spl10_70
    | ~ spl10_1376 ),
    inference(avatar_split_clause,[],[f39043,f24078,f503,f270,f39167])).

fof(f270,plain,
    ( spl10_26
  <=> r8_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f503,plain,
    ( spl10_70
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f24078,plain,
    ( spl10_1376
  <=> u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1376])])).

fof(f39043,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) )
    | ~ spl10_26
    | ~ spl10_70
    | ~ spl10_1376 ),
    inference(forward_demodulation,[],[f39042,f24079])).

fof(f24079,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl10_1376 ),
    inference(avatar_component_clause,[],[f24078])).

fof(f39042,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) )
    | ~ spl10_26
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f39040,f504])).

fof(f504,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f503])).

fof(f39040,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl10_26 ),
    inference(resolution,[],[f271,f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( ~ r8_orders_1(X0,X1)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
              & sK3(X0,X1) != X1
              & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f101,f102])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
        & sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(X2,k3_relat_1(X0))
               => ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2 ) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',d13_orders_1)).

fof(f271,plain,
    ( r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f270])).

fof(f38997,plain,
    ( spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2116 ),
    inference(avatar_contradiction_clause,[],[f38996])).

fof(f38996,plain,
    ( $false
    | ~ spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2116 ),
    inference(subsumption_resolution,[],[f38995,f415])).

fof(f38995,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2116 ),
    inference(forward_demodulation,[],[f38994,f24079])).

fof(f38994,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_2116 ),
    inference(subsumption_resolution,[],[f38993,f504])).

fof(f38993,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_27
    | ~ spl10_2116 ),
    inference(subsumption_resolution,[],[f38984,f274])).

fof(f38984,plain,
    ( r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2116 ),
    inference(resolution,[],[f38571,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
      | r8_orders_1(X0,X1)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f38571,plain,
    ( r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | ~ spl10_2116 ),
    inference(avatar_component_clause,[],[f38570])).

fof(f38570,plain,
    ( spl10_2116
  <=> r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2116])])).

fof(f38613,plain,
    ( spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2114 ),
    inference(avatar_contradiction_clause,[],[f38612])).

fof(f38612,plain,
    ( $false
    | ~ spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2114 ),
    inference(subsumption_resolution,[],[f38611,f415])).

fof(f38611,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_1376
    | ~ spl10_2114 ),
    inference(forward_demodulation,[],[f38610,f24079])).

fof(f38610,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_2114 ),
    inference(subsumption_resolution,[],[f38609,f504])).

fof(f38609,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_27
    | ~ spl10_2114 ),
    inference(subsumption_resolution,[],[f38602,f274])).

fof(f38602,plain,
    ( r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2114 ),
    inference(trivial_inequality_removal,[],[f38601])).

fof(f38601,plain,
    ( sK1 != sK1
    | r8_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2114 ),
    inference(superposition,[],[f130,f38565])).

fof(f38565,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl10_2114 ),
    inference(avatar_component_clause,[],[f38564])).

fof(f38564,plain,
    ( spl10_2114
  <=> sK1 = sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2114])])).

fof(f130,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | r8_orders_1(X0,X1)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f38572,plain,
    ( spl10_2114
    | spl10_2116
    | ~ spl10_102
    | ~ spl10_1382 ),
    inference(avatar_split_clause,[],[f24306,f24289,f708,f38570,f38564])).

fof(f708,plain,
    ( spl10_102
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f24289,plain,
    ( spl10_1382
  <=> m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1382])])).

fof(f24306,plain,
    ( r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),sK1),sK1),u1_orders_2(sK0))
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl10_102
    | ~ spl10_1382 ),
    inference(resolution,[],[f24290,f709])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f708])).

fof(f24290,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_1382 ),
    inference(avatar_component_clause,[],[f24289])).

fof(f24593,plain,
    ( spl10_1402
    | ~ spl10_1388 ),
    inference(avatar_split_clause,[],[f24433,f24429,f24591])).

fof(f24429,plain,
    ( spl10_1388
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1388])])).

fof(f24433,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0)
        | m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0)) )
    | ~ spl10_1388 ),
    inference(resolution,[],[f24430,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',t1_subset)).

fof(f24430,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_1388 ),
    inference(avatar_component_clause,[],[f24429])).

fof(f24431,plain,
    ( spl10_1388
    | ~ spl10_298
    | ~ spl10_1376 ),
    inference(avatar_split_clause,[],[f24209,f24078,f2919,f24429])).

fof(f2919,plain,
    ( spl10_298
  <=> ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r8_orders_1(u1_orders_2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_298])])).

fof(f24209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | r8_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_298
    | ~ spl10_1376 ),
    inference(forward_demodulation,[],[f24193,f24079])).

fof(f24193,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r8_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_298
    | ~ spl10_1376 ),
    inference(backward_demodulation,[],[f24079,f2920])).

fof(f2920,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | r8_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_298 ),
    inference(avatar_component_clause,[],[f2919])).

fof(f24089,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | spl10_1375 ),
    inference(avatar_contradiction_clause,[],[f24088])).

fof(f24088,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_1375 ),
    inference(subsumption_resolution,[],[f24087,f209])).

fof(f24087,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_2
    | ~ spl10_1375 ),
    inference(subsumption_resolution,[],[f24085,f188])).

fof(f188,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl10_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f24085,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_1375 ),
    inference(resolution,[],[f24073,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',cc1_orders_2)).

fof(f24073,plain,
    ( ~ v2_orders_2(sK0)
    | ~ spl10_1375 ),
    inference(avatar_component_clause,[],[f24072])).

fof(f24072,plain,
    ( spl10_1375
  <=> ~ v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1375])])).

fof(f23750,plain,
    ( spl10_1344
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f7624,f208,f201,f194,f187,f23748])).

fof(f194,plain,
    ( spl10_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f201,plain,
    ( spl10_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f7624,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0 )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f7623,f188])).

fof(f7623,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f7622,f195])).

fof(f195,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f194])).

fof(f7622,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | ~ v4_orders_2(sK0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f7621,f209])).

fof(f7621,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f988,f202])).

fof(f202,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f988,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f987,f134])).

fof(f987,plain,(
    ! [X0,X1] :
      ( k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f986])).

fof(f986,plain,(
    ! [X0,X1] :
      ( k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f590,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',fc3_orders_2)).

fof(f590,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(u1_orders_2(X0))
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f589])).

fof(f589,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f427,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',fc4_orders_2)).

fof(f427,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(u1_orders_2(X0))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f152,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',fc5_orders_2)).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k3_relat_1(X1) = X0
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',t100_orders_1)).

fof(f3280,plain,
    ( ~ spl10_331
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f3266,f270,f3278])).

fof(f3266,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f124,f271])).

fof(f124,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,
    ( ( ( ~ r2_orders_2(sK0,sK2,sK1)
        & sK1 != sK2
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ r8_orders_1(u1_orders_2(sK0),sK1) )
    & ( ! [X3] :
          ( r2_orders_2(sK0,X3,sK1)
          | sK1 = X3
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | r8_orders_1(u1_orders_2(sK0),sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f94,f97,f96,f95])).

fof(f95,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_orders_2(X0,X2,X1)
                  & X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r8_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( r2_orders_2(X0,X3,X1)
                  | X1 = X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r8_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(sK0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r8_orders_1(u1_orders_2(sK0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(sK0,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | r8_orders_1(u1_orders_2(sK0),X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ? [X2] :
              ( ~ r2_orders_2(X0,X2,sK1)
              & sK1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r8_orders_1(u1_orders_2(X0),sK1) )
        & ( ! [X3] :
              ( r2_orders_2(X0,X3,sK1)
              | sK1 = X3
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | r8_orders_1(u1_orders_2(X0),sK1) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_orders_2(X0,X2,X1)
          & X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK2,X1)
        & sK2 != X1
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
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
           => ( r8_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( X1 != X2
                   => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
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
         => ( r8_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( X1 != X2
                 => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',t160_orders_2)).

fof(f2921,plain,
    ( spl10_298
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f513,f503,f2919])).

fof(f513,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r8_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_70 ),
    inference(resolution,[],[f504,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | r8_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f732,plain,
    ( spl10_104
    | ~ spl10_50
    | spl10_59 ),
    inference(avatar_split_clause,[],[f725,f417,f380,f730])).

fof(f417,plain,
    ( spl10_59
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f725,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_50
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f720,f418])).

fof(f418,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f417])).

fof(f720,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(resolution,[],[f381,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',t2_subset)).

fof(f710,plain,
    ( spl10_102
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f581,f364,f236,f208,f708])).

fof(f364,plain,
    ( spl10_46
  <=> ! [X3] :
        ( r2_orders_2(sK0,X3,sK1)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f580,f209])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f579,f237])).

fof(f579,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_46 ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | sK1 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_46 ),
    inference(resolution,[],[f442,f365])).

fof(f365,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,X3,sK1)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f364])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2)) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ r2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f135,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f550,plain,
    ( ~ spl10_8
    | spl10_79 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f547,f209])).

fof(f547,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_79 ),
    inference(resolution,[],[f540,f132])).

fof(f132,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',dt_l1_orders_2)).

fof(f540,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl10_79
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f541,plain,
    ( ~ spl10_79
    | spl10_1
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f534,f420,f180,f539])).

fof(f180,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f420,plain,
    ( spl10_58
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f534,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f530,f181])).

fof(f181,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f180])).

fof(f530,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_58 ),
    inference(resolution,[],[f421,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',fc2_struct_0)).

fof(f421,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f420])).

fof(f505,plain,
    ( spl10_70
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f494,f484,f503])).

fof(f494,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_68 ),
    inference(resolution,[],[f485,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',cc1_relset_1)).

fof(f486,plain,
    ( spl10_68
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f333,f208,f484])).

fof(f333,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_8 ),
    inference(resolution,[],[f133,f209])).

fof(f133,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t160_orders_2.p',dt_u1_orders_2)).

fof(f422,plain,
    ( spl10_56
    | spl10_58
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f303,f236,f420,f414])).

fof(f303,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(resolution,[],[f151,f237])).

fof(f382,plain,
    ( spl10_50
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f374,f270,f380])).

fof(f374,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f122,f271])).

fof(f122,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f366,plain,
    ( spl10_46
    | spl10_27 ),
    inference(avatar_split_clause,[],[f355,f273,f364])).

fof(f355,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,X3,sK1)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f121,f274])).

fof(f121,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,X3,sK1)
      | sK1 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r8_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f281,plain,
    ( ~ spl10_27
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f123,f279,f273])).

fof(f123,plain,
    ( sK1 != sK2
    | ~ r8_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f238,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f120,f236])).

fof(f120,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f98])).

fof(f210,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f119,f208])).

fof(f119,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f203,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f118,f201])).

fof(f118,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f196,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f117,f194])).

fof(f117,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f189,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f116,f187])).

fof(f116,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f182,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f115,f180])).

fof(f115,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f98])).
%------------------------------------------------------------------------------
