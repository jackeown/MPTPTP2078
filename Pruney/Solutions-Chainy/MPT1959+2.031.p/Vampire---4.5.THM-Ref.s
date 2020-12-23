%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 421 expanded)
%              Number of leaves         :   48 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  943 (2375 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f135,f140,f145,f150,f160,f165,f174,f176,f182,f191,f203,f323,f340,f396,f430,f434,f435,f450,f511,f520,f529,f539,f567,f584,f973,f1002])).

fof(f1002,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | spl8_48
    | ~ spl8_53
    | ~ spl8_96 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | spl8_48
    | ~ spl8_53
    | ~ spl8_96 ),
    inference(unit_resulting_resolution,[],[f159,f527,f566,f172,f164,f972])).

fof(f972,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(X1,sK0)
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1) )
    | ~ spl8_96 ),
    inference(avatar_component_clause,[],[f971])).

fof(f971,plain,
    ( spl8_96
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f164,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f172,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f566,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl8_53
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f527,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | spl8_48 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl8_48
  <=> r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f159,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl8_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f973,plain,
    ( spl8_96
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f601,f509,f428,f971])).

fof(f428,plain,
    ( spl8_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f509,plain,
    ( spl8_46
  <=> ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f601,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ v13_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1) )
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X1) )
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(resolution,[],[f510,f429])).

fof(f429,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f428])).

fof(f510,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f509])).

fof(f584,plain,
    ( ~ spl8_10
    | spl8_47
    | ~ spl8_48 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl8_10
    | spl8_47
    | ~ spl8_48 ),
    inference(unit_resulting_resolution,[],[f164,f528,f523,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f523,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl8_47
  <=> r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f528,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f526])).

fof(f567,plain,
    ( spl8_53
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f535,f522,f564])).

fof(f535,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_47 ),
    inference(resolution,[],[f524,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f524,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f522])).

fof(f539,plain,
    ( ~ spl8_48
    | ~ spl8_10
    | spl8_15
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f538,f522,f200,f162,f526])).

fof(f200,plain,
    ( spl8_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f538,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl8_10
    | spl8_15
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f537,f164])).

fof(f537,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_15
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f536,f220])).

fof(f220,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f100,f195])).

fof(f195,plain,(
    ! [X0] : sK6(X0) = X0 ),
    inference(subsumption_resolution,[],[f193,f101])).

fof(f101,plain,(
    ! [X0] : ~ v1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK6(X0),X0)
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f193,plain,(
    ! [X0] :
      ( sK6(X0) = X0
      | v1_subset_1(sK6(X0),X0) ) ),
    inference(resolution,[],[f106,f100])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f536,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_15
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f532,f201])).

fof(f201,plain,
    ( u1_struct_0(sK0) != sK1
    | spl8_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f532,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_47 ),
    inference(resolution,[],[f524,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK7(X0,X1,X2),X2)
              | ~ r2_hidden(sK7(X0,X1,X2),X1) )
            & ( r2_hidden(sK7(X0,X1,X2),X2)
              | r2_hidden(sK7(X0,X1,X2),X1) )
            & m1_subset_1(sK7(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X2)
          | ~ r2_hidden(sK7(X0,X1,X2),X1) )
        & ( r2_hidden(sK7(X0,X1,X2),X2)
          | r2_hidden(sK7(X0,X1,X2),X1) )
        & m1_subset_1(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f529,plain,
    ( spl8_47
    | spl8_48
    | spl8_15
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f443,f423,f200,f526,f522])).

fof(f423,plain,
    ( spl8_38
  <=> ! [X0] :
        ( r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0)
        | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f443,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl8_15
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f440,f201])).

fof(f440,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl8_38 ),
    inference(resolution,[],[f424,f220])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1)
        | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0)
        | sK1 = X0 )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f423])).

fof(f520,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_45 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_45 ),
    inference(subsumption_resolution,[],[f518,f119])).

fof(f119,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f518,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_45 ),
    inference(subsumption_resolution,[],[f517,f134])).

fof(f134,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f517,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_45 ),
    inference(subsumption_resolution,[],[f516,f139])).

fof(f139,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f516,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | spl8_45 ),
    inference(subsumption_resolution,[],[f514,f144])).

fof(f144,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f514,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_45 ),
    inference(resolution,[],[f507,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f507,plain,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | spl8_45 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl8_45
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f511,plain,
    ( ~ spl8_45
    | spl8_46
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f461,f448,f179,f142,f509,f505])).

fof(f179,plain,
    ( spl8_13
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f448,plain,
    ( spl8_42
  <=> ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f461,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0) )
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f460,f181])).

fof(f181,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ r1_yellow_0(sK0,k1_xboole_0) )
    | ~ spl8_6
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f459,f144])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_42 ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_42 ),
    inference(resolution,[],[f449,f278])).

fof(f278,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f449,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f448])).

fof(f450,plain,
    ( spl8_42
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f444,f432,f448])).

fof(f432,plain,
    ( spl8_40
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X4,X3)
        | ~ r1_tarski(X4,sK5(sK0,X4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f444,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_40 ),
    inference(resolution,[],[f433,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f433,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,sK5(sK0,X4,X3))
        | r2_lattice3(sK0,X4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f432])).

fof(f435,plain,
    ( spl8_38
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f344,f162,f423])).

fof(f344,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0)
        | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl8_10 ),
    inference(resolution,[],[f164,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f434,plain,
    ( spl8_40
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f403,f394,f432])).

fof(f394,plain,
    ( spl8_33
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f403,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X4,X3)
        | ~ r1_tarski(X4,sK5(sK0,X4,X3)) )
    | ~ spl8_33 ),
    inference(resolution,[],[f395,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f395,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f394])).

fof(f430,plain,
    ( spl8_39
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f299,f142,f428])).

fof(f299,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f290,f144])).

fof(f290,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f83,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f396,plain,
    ( spl8_33
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f232,f142,f394])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f144])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f340,plain,
    ( ~ spl8_11
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f338,f221])).

fof(f221,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f101,f195])).

fof(f338,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f169,f202])).

fof(f202,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f169,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f323,plain,
    ( ~ spl8_6
    | spl8_14
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl8_6
    | spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f321,f144])).

fof(f321,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f314,f190])).

fof(f190,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_14
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f314,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl8_15 ),
    inference(superposition,[],[f81,f202])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f203,plain,
    ( spl8_15
    | ~ spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f194,f167,f162,f200])).

fof(f194,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f192,f168])).

fof(f168,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f192,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(resolution,[],[f106,f164])).

fof(f191,plain,
    ( ~ spl8_14
    | spl8_7
    | spl8_12 ),
    inference(avatar_split_clause,[],[f186,f171,f147,f188])).

fof(f147,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f186,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl8_7
    | spl8_12 ),
    inference(subsumption_resolution,[],[f185,f149])).

fof(f149,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f185,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl8_12 ),
    inference(resolution,[],[f104,f173])).

fof(f173,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f182,plain,
    ( spl8_13
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f177,f142,f179])).

fof(f177,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f82,f144])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f176,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f175,f171,f167])).

fof(f175,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_12 ),
    inference(subsumption_resolution,[],[f79,f173])).

fof(f79,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f174,plain,
    ( spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f78,f171,f167])).

fof(f78,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f165,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f77,f162])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f160,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f76,f157])).

fof(f76,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f150,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f74,f147])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f145,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f73,f142])).

fof(f73,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f140,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f72,f137])).

fof(f72,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f135,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f71,f132])).

fof(f71,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f120,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f68,f117])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:17:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (3587)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (3589)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (3585)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (3603)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (3596)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (3602)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (3605)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.55  % (3595)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (3598)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (3604)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (3588)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (3594)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (3593)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (3586)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (3589)Refutation not found, incomplete strategy% (3589)------------------------------
% 0.22/0.56  % (3589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (3591)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.56/0.57  % (3589)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  % (3601)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.56/0.57  
% 1.56/0.57  % (3589)Memory used [KB]: 10746
% 1.56/0.57  % (3589)Time elapsed: 0.125 s
% 1.56/0.57  % (3589)------------------------------
% 1.56/0.57  % (3589)------------------------------
% 1.56/0.57  % (3607)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.56/0.58  % (3608)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.56/0.58  % (3606)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.72/0.59  % (3599)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.72/0.59  % (3592)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.72/0.59  % (3597)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.72/0.59  % (3590)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.72/0.59  % (3583)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.72/0.59  % (3600)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.72/0.59  % (3582)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.72/0.60  % (3582)Refutation not found, incomplete strategy% (3582)------------------------------
% 1.72/0.60  % (3582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (3582)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (3582)Memory used [KB]: 10618
% 1.72/0.60  % (3582)Time elapsed: 0.158 s
% 1.72/0.60  % (3582)------------------------------
% 1.72/0.60  % (3582)------------------------------
% 1.72/0.60  % (3590)Refutation not found, incomplete strategy% (3590)------------------------------
% 1.72/0.60  % (3590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (3590)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (3590)Memory used [KB]: 1663
% 1.72/0.60  % (3590)Time elapsed: 0.167 s
% 1.72/0.60  % (3590)------------------------------
% 1.72/0.60  % (3590)------------------------------
% 1.72/0.62  % (3585)Refutation found. Thanks to Tanya!
% 1.72/0.62  % SZS status Theorem for theBenchmark
% 1.72/0.64  % SZS output start Proof for theBenchmark
% 1.72/0.64  fof(f1007,plain,(
% 1.72/0.64    $false),
% 1.72/0.64    inference(avatar_sat_refutation,[],[f120,f135,f140,f145,f150,f160,f165,f174,f176,f182,f191,f203,f323,f340,f396,f430,f434,f435,f450,f511,f520,f529,f539,f567,f584,f973,f1002])).
% 1.72/0.64  fof(f1002,plain,(
% 1.72/0.64    ~spl8_9 | ~spl8_10 | ~spl8_12 | spl8_48 | ~spl8_53 | ~spl8_96),
% 1.72/0.64    inference(avatar_contradiction_clause,[],[f999])).
% 1.72/0.64  fof(f999,plain,(
% 1.72/0.64    $false | (~spl8_9 | ~spl8_10 | ~spl8_12 | spl8_48 | ~spl8_53 | ~spl8_96)),
% 1.72/0.64    inference(unit_resulting_resolution,[],[f159,f527,f566,f172,f164,f972])).
% 1.72/0.64  fof(f972,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~v13_waybel_0(X1,sK0) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1)) ) | ~spl8_96),
% 1.72/0.64    inference(avatar_component_clause,[],[f971])).
% 1.72/0.64  fof(f971,plain,(
% 1.72/0.64    spl8_96 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~v13_waybel_0(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).
% 1.72/0.64  fof(f164,plain,(
% 1.72/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_10),
% 1.72/0.64    inference(avatar_component_clause,[],[f162])).
% 1.72/0.64  fof(f162,plain,(
% 1.72/0.64    spl8_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.72/0.64  fof(f172,plain,(
% 1.72/0.64    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_12),
% 1.72/0.64    inference(avatar_component_clause,[],[f171])).
% 1.72/0.64  fof(f171,plain,(
% 1.72/0.64    spl8_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.72/0.64  fof(f566,plain,(
% 1.72/0.64    m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl8_53),
% 1.72/0.64    inference(avatar_component_clause,[],[f564])).
% 1.72/0.64  fof(f564,plain,(
% 1.72/0.64    spl8_53 <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.72/0.64  fof(f527,plain,(
% 1.72/0.64    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | spl8_48),
% 1.72/0.64    inference(avatar_component_clause,[],[f526])).
% 1.72/0.64  fof(f526,plain,(
% 1.72/0.64    spl8_48 <=> r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.72/0.64  fof(f159,plain,(
% 1.72/0.64    v13_waybel_0(sK1,sK0) | ~spl8_9),
% 1.72/0.64    inference(avatar_component_clause,[],[f157])).
% 1.72/0.64  fof(f157,plain,(
% 1.72/0.64    spl8_9 <=> v13_waybel_0(sK1,sK0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.72/0.64  fof(f973,plain,(
% 1.72/0.64    spl8_96 | ~spl8_39 | ~spl8_46),
% 1.72/0.64    inference(avatar_split_clause,[],[f601,f509,f428,f971])).
% 1.72/0.64  fof(f428,plain,(
% 1.72/0.64    spl8_39 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.72/0.64  fof(f509,plain,(
% 1.72/0.64    spl8_46 <=> ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.72/0.64  fof(f601,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~v13_waybel_0(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1)) ) | (~spl8_39 | ~spl8_46)),
% 1.72/0.64    inference(duplicate_literal_removal,[],[f599])).
% 1.72/0.64  fof(f599,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1)) ) | (~spl8_39 | ~spl8_46)),
% 1.72/0.64    inference(resolution,[],[f510,f429])).
% 1.72/0.64  fof(f429,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_39),
% 1.72/0.64    inference(avatar_component_clause,[],[f428])).
% 1.72/0.64  fof(f510,plain,(
% 1.72/0.64    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_46),
% 1.72/0.64    inference(avatar_component_clause,[],[f509])).
% 1.72/0.64  fof(f584,plain,(
% 1.72/0.64    ~spl8_10 | spl8_47 | ~spl8_48),
% 1.72/0.64    inference(avatar_contradiction_clause,[],[f582])).
% 1.72/0.64  fof(f582,plain,(
% 1.72/0.64    $false | (~spl8_10 | spl8_47 | ~spl8_48)),
% 1.72/0.64    inference(unit_resulting_resolution,[],[f164,f528,f523,f107])).
% 1.72/0.64  fof(f107,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.72/0.64    inference(cnf_transformation,[],[f36])).
% 1.72/0.64  fof(f36,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(ennf_transformation,[],[f2])).
% 1.72/0.64  fof(f2,axiom,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.72/0.64  fof(f523,plain,(
% 1.72/0.64    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | spl8_47),
% 1.72/0.64    inference(avatar_component_clause,[],[f522])).
% 1.72/0.64  fof(f522,plain,(
% 1.72/0.64    spl8_47 <=> r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.72/0.64  fof(f528,plain,(
% 1.72/0.64    r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~spl8_48),
% 1.72/0.64    inference(avatar_component_clause,[],[f526])).
% 1.72/0.64  fof(f567,plain,(
% 1.72/0.64    spl8_53 | ~spl8_47),
% 1.72/0.64    inference(avatar_split_clause,[],[f535,f522,f564])).
% 1.72/0.64  fof(f535,plain,(
% 1.72/0.64    m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl8_47),
% 1.72/0.64    inference(resolution,[],[f524,f103])).
% 1.72/0.64  fof(f103,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f32])).
% 1.72/0.64  fof(f32,plain,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.72/0.64    inference(ennf_transformation,[],[f5])).
% 1.72/0.64  fof(f5,axiom,(
% 1.72/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.72/0.64  fof(f524,plain,(
% 1.72/0.64    r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl8_47),
% 1.72/0.64    inference(avatar_component_clause,[],[f522])).
% 1.72/0.64  fof(f539,plain,(
% 1.72/0.64    ~spl8_48 | ~spl8_10 | spl8_15 | ~spl8_47),
% 1.72/0.64    inference(avatar_split_clause,[],[f538,f522,f200,f162,f526])).
% 1.72/0.64  fof(f200,plain,(
% 1.72/0.64    spl8_15 <=> u1_struct_0(sK0) = sK1),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.72/0.64  fof(f538,plain,(
% 1.72/0.64    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | (~spl8_10 | spl8_15 | ~spl8_47)),
% 1.72/0.64    inference(subsumption_resolution,[],[f537,f164])).
% 1.72/0.64  fof(f537,plain,(
% 1.72/0.64    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_15 | ~spl8_47)),
% 1.72/0.64    inference(subsumption_resolution,[],[f536,f220])).
% 1.72/0.64  fof(f220,plain,(
% 1.72/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.72/0.64    inference(backward_demodulation,[],[f100,f195])).
% 1.72/0.64  fof(f195,plain,(
% 1.72/0.64    ( ! [X0] : (sK6(X0) = X0) )),
% 1.72/0.64    inference(subsumption_resolution,[],[f193,f101])).
% 1.72/0.64  fof(f101,plain,(
% 1.72/0.64    ( ! [X0] : (~v1_subset_1(sK6(X0),X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f62])).
% 1.72/0.64  fof(f62,plain,(
% 1.72/0.64    ! [X0] : (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f61])).
% 1.72/0.64  fof(f61,plain,(
% 1.72/0.64    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f4,axiom,(
% 1.72/0.64    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.72/0.64  fof(f193,plain,(
% 1.72/0.64    ( ! [X0] : (sK6(X0) = X0 | v1_subset_1(sK6(X0),X0)) )),
% 1.72/0.64    inference(resolution,[],[f106,f100])).
% 1.72/0.64  fof(f106,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f63])).
% 1.72/0.64  fof(f63,plain,(
% 1.72/0.64    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(nnf_transformation,[],[f35])).
% 1.72/0.64  fof(f35,plain,(
% 1.72/0.64    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(ennf_transformation,[],[f16])).
% 1.72/0.64  fof(f16,axiom,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.72/0.64  fof(f100,plain,(
% 1.72/0.64    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) )),
% 1.72/0.64    inference(cnf_transformation,[],[f62])).
% 1.72/0.64  fof(f536,plain,(
% 1.72/0.64    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl8_15 | ~spl8_47)),
% 1.72/0.64    inference(subsumption_resolution,[],[f532,f201])).
% 1.72/0.64  fof(f201,plain,(
% 1.72/0.64    u1_struct_0(sK0) != sK1 | spl8_15),
% 1.72/0.64    inference(avatar_component_clause,[],[f200])).
% 1.72/0.64  fof(f532,plain,(
% 1.72/0.64    u1_struct_0(sK0) = sK1 | ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_47),
% 1.72/0.64    inference(resolution,[],[f524,f110])).
% 1.72/0.64  fof(f110,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK7(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.72/0.64    inference(cnf_transformation,[],[f67])).
% 1.72/0.64  fof(f67,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(sK7(X0,X1,X2),X1)) & (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f65,f66])).
% 1.72/0.64  fof(f66,plain,(
% 1.72/0.64    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(sK7(X0,X1,X2),X1)) & (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),X0)))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f65,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(flattening,[],[f64])).
% 1.72/0.64  fof(f64,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(nnf_transformation,[],[f38])).
% 1.72/0.64  fof(f38,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(flattening,[],[f37])).
% 1.72/0.64  fof(f37,plain,(
% 1.72/0.64    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.64    inference(ennf_transformation,[],[f3])).
% 1.72/0.64  fof(f3,axiom,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.72/0.64  fof(f529,plain,(
% 1.72/0.64    spl8_47 | spl8_48 | spl8_15 | ~spl8_38),
% 1.72/0.64    inference(avatar_split_clause,[],[f443,f423,f200,f526,f522])).
% 1.72/0.64  fof(f423,plain,(
% 1.72/0.64    spl8_38 <=> ! [X0] : (r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0) | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.72/0.64  fof(f443,plain,(
% 1.72/0.64    r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (spl8_15 | ~spl8_38)),
% 1.72/0.64    inference(subsumption_resolution,[],[f440,f201])).
% 1.72/0.64  fof(f440,plain,(
% 1.72/0.64    r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl8_38),
% 1.72/0.64    inference(resolution,[],[f424,f220])).
% 1.72/0.64  fof(f424,plain,(
% 1.72/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1) | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0) | sK1 = X0) ) | ~spl8_38),
% 1.72/0.64    inference(avatar_component_clause,[],[f423])).
% 1.72/0.64  fof(f520,plain,(
% 1.72/0.64    spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_45),
% 1.72/0.64    inference(avatar_contradiction_clause,[],[f519])).
% 1.72/0.64  fof(f519,plain,(
% 1.72/0.64    $false | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_45)),
% 1.72/0.64    inference(subsumption_resolution,[],[f518,f119])).
% 1.72/0.64  fof(f119,plain,(
% 1.72/0.64    ~v2_struct_0(sK0) | spl8_1),
% 1.72/0.64    inference(avatar_component_clause,[],[f117])).
% 1.72/0.64  fof(f117,plain,(
% 1.72/0.64    spl8_1 <=> v2_struct_0(sK0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.72/0.64  fof(f518,plain,(
% 1.72/0.64    v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_45)),
% 1.72/0.64    inference(subsumption_resolution,[],[f517,f134])).
% 1.72/0.64  fof(f134,plain,(
% 1.72/0.64    v5_orders_2(sK0) | ~spl8_4),
% 1.72/0.64    inference(avatar_component_clause,[],[f132])).
% 1.72/0.64  fof(f132,plain,(
% 1.72/0.64    spl8_4 <=> v5_orders_2(sK0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.72/0.64  fof(f517,plain,(
% 1.72/0.64    ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_6 | spl8_45)),
% 1.72/0.64    inference(subsumption_resolution,[],[f516,f139])).
% 1.72/0.64  fof(f139,plain,(
% 1.72/0.64    v1_yellow_0(sK0) | ~spl8_5),
% 1.72/0.64    inference(avatar_component_clause,[],[f137])).
% 1.72/0.64  fof(f137,plain,(
% 1.72/0.64    spl8_5 <=> v1_yellow_0(sK0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.72/0.64  fof(f516,plain,(
% 1.72/0.64    ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_6 | spl8_45)),
% 1.72/0.64    inference(subsumption_resolution,[],[f514,f144])).
% 1.72/0.64  fof(f144,plain,(
% 1.72/0.64    l1_orders_2(sK0) | ~spl8_6),
% 1.72/0.64    inference(avatar_component_clause,[],[f142])).
% 1.72/0.64  fof(f142,plain,(
% 1.72/0.64    spl8_6 <=> l1_orders_2(sK0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.72/0.64  fof(f514,plain,(
% 1.72/0.64    ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_45),
% 1.72/0.64    inference(resolution,[],[f507,f98])).
% 1.72/0.64  fof(f98,plain,(
% 1.72/0.64    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f30])).
% 1.72/0.64  fof(f30,plain,(
% 1.72/0.64    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.72/0.64    inference(flattening,[],[f29])).
% 1.72/0.64  fof(f29,plain,(
% 1.72/0.64    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.72/0.64    inference(ennf_transformation,[],[f14])).
% 1.72/0.64  fof(f14,axiom,(
% 1.72/0.64    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.72/0.64  fof(f507,plain,(
% 1.72/0.64    ~r1_yellow_0(sK0,k1_xboole_0) | spl8_45),
% 1.72/0.64    inference(avatar_component_clause,[],[f505])).
% 1.72/0.64  fof(f505,plain,(
% 1.72/0.64    spl8_45 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.72/0.64  fof(f511,plain,(
% 1.72/0.64    ~spl8_45 | spl8_46 | ~spl8_6 | ~spl8_13 | ~spl8_42),
% 1.72/0.64    inference(avatar_split_clause,[],[f461,f448,f179,f142,f509,f505])).
% 1.72/0.64  fof(f179,plain,(
% 1.72/0.64    spl8_13 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.72/0.64  fof(f448,plain,(
% 1.72/0.64    spl8_42 <=> ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.72/0.64  fof(f461,plain,(
% 1.72/0.64    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0)) ) | (~spl8_6 | ~spl8_13 | ~spl8_42)),
% 1.72/0.64    inference(forward_demodulation,[],[f460,f181])).
% 1.72/0.64  fof(f181,plain,(
% 1.72/0.64    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_13),
% 1.72/0.64    inference(avatar_component_clause,[],[f179])).
% 1.72/0.64  fof(f460,plain,(
% 1.72/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~r1_yellow_0(sK0,k1_xboole_0)) ) | (~spl8_6 | ~spl8_42)),
% 1.72/0.64    inference(subsumption_resolution,[],[f459,f144])).
% 1.72/0.64  fof(f459,plain,(
% 1.72/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_42),
% 1.72/0.64    inference(duplicate_literal_removal,[],[f454])).
% 1.72/0.64  fof(f454,plain,(
% 1.72/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_42),
% 1.72/0.64    inference(resolution,[],[f449,f278])).
% 1.72/0.64  fof(f278,plain,(
% 1.72/0.64    ( ! [X4,X0,X1] : (~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(subsumption_resolution,[],[f113,f102])).
% 1.72/0.64  fof(f102,plain,(
% 1.72/0.64    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f31])).
% 1.72/0.64  fof(f31,plain,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f12])).
% 1.72/0.64  fof(f12,axiom,(
% 1.72/0.64    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.72/0.64  fof(f113,plain,(
% 1.72/0.64    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(equality_resolution,[],[f90])).
% 1.72/0.64  fof(f90,plain,(
% 1.72/0.64    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f56])).
% 1.72/0.64  fof(f56,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 1.72/0.64  fof(f55,plain,(
% 1.72/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f54,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(rectify,[],[f53])).
% 1.72/0.64  fof(f53,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(flattening,[],[f52])).
% 1.72/0.64  fof(f52,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(nnf_transformation,[],[f26])).
% 1.72/0.64  fof(f26,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(flattening,[],[f25])).
% 1.72/0.64  fof(f25,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f11])).
% 1.72/0.64  fof(f11,axiom,(
% 1.72/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.72/0.64  fof(f449,plain,(
% 1.72/0.64    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_42),
% 1.72/0.64    inference(avatar_component_clause,[],[f448])).
% 1.72/0.64  fof(f450,plain,(
% 1.72/0.64    spl8_42 | ~spl8_40),
% 1.72/0.64    inference(avatar_split_clause,[],[f444,f432,f448])).
% 1.72/0.64  fof(f432,plain,(
% 1.72/0.64    spl8_40 <=> ! [X3,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,X4,X3) | ~r1_tarski(X4,sK5(sK0,X4,X3)))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.72/0.64  fof(f444,plain,(
% 1.72/0.64    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_40),
% 1.72/0.64    inference(resolution,[],[f433,f80])).
% 1.72/0.64  fof(f80,plain,(
% 1.72/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f1])).
% 1.72/0.64  fof(f1,axiom,(
% 1.72/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.72/0.64  fof(f433,plain,(
% 1.72/0.64    ( ! [X4,X3] : (~r1_tarski(X4,sK5(sK0,X4,X3)) | r2_lattice3(sK0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl8_40),
% 1.72/0.64    inference(avatar_component_clause,[],[f432])).
% 1.72/0.64  fof(f435,plain,(
% 1.72/0.64    spl8_38 | ~spl8_10),
% 1.72/0.64    inference(avatar_split_clause,[],[f344,f162,f423])).
% 1.72/0.64  fof(f344,plain,(
% 1.72/0.64    ( ! [X0] : (r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),X0) | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | ~spl8_10),
% 1.72/0.64    inference(resolution,[],[f164,f109])).
% 1.72/0.64  fof(f109,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.72/0.64    inference(cnf_transformation,[],[f67])).
% 1.72/0.64  fof(f434,plain,(
% 1.72/0.64    spl8_40 | ~spl8_33),
% 1.72/0.64    inference(avatar_split_clause,[],[f403,f394,f432])).
% 1.72/0.64  fof(f394,plain,(
% 1.72/0.64    spl8_33 <=> ! [X1,X0] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.72/0.64  fof(f403,plain,(
% 1.72/0.64    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,X4,X3) | ~r1_tarski(X4,sK5(sK0,X4,X3))) ) | ~spl8_33),
% 1.72/0.64    inference(resolution,[],[f395,f111])).
% 1.72/0.64  fof(f111,plain,(
% 1.72/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f39])).
% 1.72/0.64  fof(f39,plain,(
% 1.72/0.64    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.72/0.64    inference(ennf_transformation,[],[f8])).
% 1.72/0.64  fof(f8,axiom,(
% 1.72/0.64    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.72/0.64  fof(f395,plain,(
% 1.72/0.64    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_33),
% 1.72/0.64    inference(avatar_component_clause,[],[f394])).
% 1.72/0.64  fof(f430,plain,(
% 1.72/0.64    spl8_39 | ~spl8_6),
% 1.72/0.64    inference(avatar_split_clause,[],[f299,f142,f428])).
% 1.72/0.64  fof(f299,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_6),
% 1.72/0.64    inference(resolution,[],[f290,f144])).
% 1.72/0.64  fof(f290,plain,(
% 1.72/0.64    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.72/0.64    inference(subsumption_resolution,[],[f83,f112])).
% 1.72/0.64  fof(f112,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f41])).
% 1.72/0.64  fof(f41,plain,(
% 1.72/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.72/0.64    inference(flattening,[],[f40])).
% 1.72/0.64  fof(f40,plain,(
% 1.72/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.72/0.64    inference(ennf_transformation,[],[f7])).
% 1.72/0.64  fof(f7,axiom,(
% 1.72/0.64    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.72/0.64  fof(f83,plain,(
% 1.72/0.64    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f51])).
% 1.72/0.64  fof(f51,plain,(
% 1.72/0.64    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).
% 1.72/0.64  fof(f49,plain,(
% 1.72/0.64    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f50,plain,(
% 1.72/0.64    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f48,plain,(
% 1.72/0.64    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(rectify,[],[f47])).
% 1.72/0.64  fof(f47,plain,(
% 1.72/0.64    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(nnf_transformation,[],[f24])).
% 1.72/0.64  fof(f24,plain,(
% 1.72/0.64    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(flattening,[],[f23])).
% 1.72/0.64  fof(f23,plain,(
% 1.72/0.64    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f15])).
% 1.72/0.64  fof(f15,axiom,(
% 1.72/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.72/0.64  fof(f396,plain,(
% 1.72/0.64    spl8_33 | ~spl8_6),
% 1.72/0.64    inference(avatar_split_clause,[],[f232,f142,f394])).
% 1.72/0.64  fof(f232,plain,(
% 1.72/0.64    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_6),
% 1.72/0.64    inference(resolution,[],[f96,f144])).
% 1.72/0.64  fof(f96,plain,(
% 1.72/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f60])).
% 1.72/0.64  fof(f60,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).
% 1.72/0.64  fof(f59,plain,(
% 1.72/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f58,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(rectify,[],[f57])).
% 1.72/0.64  fof(f57,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(nnf_transformation,[],[f28])).
% 1.72/0.64  fof(f28,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(flattening,[],[f27])).
% 1.72/0.64  fof(f27,plain,(
% 1.72/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f9])).
% 1.72/0.64  fof(f9,axiom,(
% 1.72/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.72/0.64  fof(f340,plain,(
% 1.72/0.64    ~spl8_11 | ~spl8_15),
% 1.72/0.64    inference(avatar_contradiction_clause,[],[f339])).
% 1.72/0.64  fof(f339,plain,(
% 1.72/0.64    $false | (~spl8_11 | ~spl8_15)),
% 1.72/0.64    inference(subsumption_resolution,[],[f338,f221])).
% 1.72/0.64  fof(f221,plain,(
% 1.72/0.64    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.72/0.64    inference(backward_demodulation,[],[f101,f195])).
% 1.72/0.64  fof(f338,plain,(
% 1.72/0.64    v1_subset_1(sK1,sK1) | (~spl8_11 | ~spl8_15)),
% 1.72/0.64    inference(forward_demodulation,[],[f169,f202])).
% 1.72/0.64  fof(f202,plain,(
% 1.72/0.64    u1_struct_0(sK0) = sK1 | ~spl8_15),
% 1.72/0.64    inference(avatar_component_clause,[],[f200])).
% 1.72/0.64  fof(f169,plain,(
% 1.72/0.64    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_11),
% 1.72/0.64    inference(avatar_component_clause,[],[f167])).
% 1.72/0.64  fof(f167,plain,(
% 1.72/0.64    spl8_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.72/0.64  fof(f323,plain,(
% 1.72/0.64    ~spl8_6 | spl8_14 | ~spl8_15),
% 1.72/0.64    inference(avatar_contradiction_clause,[],[f322])).
% 1.72/0.64  fof(f322,plain,(
% 1.72/0.64    $false | (~spl8_6 | spl8_14 | ~spl8_15)),
% 1.72/0.64    inference(subsumption_resolution,[],[f321,f144])).
% 1.72/0.64  fof(f321,plain,(
% 1.72/0.64    ~l1_orders_2(sK0) | (spl8_14 | ~spl8_15)),
% 1.72/0.64    inference(subsumption_resolution,[],[f314,f190])).
% 1.72/0.64  fof(f190,plain,(
% 1.72/0.64    ~m1_subset_1(k3_yellow_0(sK0),sK1) | spl8_14),
% 1.72/0.64    inference(avatar_component_clause,[],[f188])).
% 1.72/0.64  fof(f188,plain,(
% 1.72/0.64    spl8_14 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.72/0.64  fof(f314,plain,(
% 1.72/0.64    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0) | ~spl8_15),
% 1.72/0.64    inference(superposition,[],[f81,f202])).
% 1.72/0.64  fof(f81,plain,(
% 1.72/0.64    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f21])).
% 1.72/0.64  fof(f21,plain,(
% 1.72/0.64    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f13])).
% 1.72/0.64  fof(f13,axiom,(
% 1.72/0.64    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.72/0.64  fof(f203,plain,(
% 1.72/0.64    spl8_15 | ~spl8_10 | spl8_11),
% 1.72/0.64    inference(avatar_split_clause,[],[f194,f167,f162,f200])).
% 1.72/0.64  fof(f194,plain,(
% 1.72/0.64    u1_struct_0(sK0) = sK1 | (~spl8_10 | spl8_11)),
% 1.72/0.64    inference(subsumption_resolution,[],[f192,f168])).
% 1.72/0.64  fof(f168,plain,(
% 1.72/0.64    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_11),
% 1.72/0.64    inference(avatar_component_clause,[],[f167])).
% 1.72/0.64  fof(f192,plain,(
% 1.72/0.64    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_10),
% 1.72/0.64    inference(resolution,[],[f106,f164])).
% 1.72/0.64  fof(f191,plain,(
% 1.72/0.64    ~spl8_14 | spl8_7 | spl8_12),
% 1.72/0.64    inference(avatar_split_clause,[],[f186,f171,f147,f188])).
% 1.72/0.64  fof(f147,plain,(
% 1.72/0.64    spl8_7 <=> v1_xboole_0(sK1)),
% 1.72/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.72/0.64  fof(f186,plain,(
% 1.72/0.64    ~m1_subset_1(k3_yellow_0(sK0),sK1) | (spl8_7 | spl8_12)),
% 1.72/0.64    inference(subsumption_resolution,[],[f185,f149])).
% 1.72/0.64  fof(f149,plain,(
% 1.72/0.64    ~v1_xboole_0(sK1) | spl8_7),
% 1.72/0.64    inference(avatar_component_clause,[],[f147])).
% 1.72/0.64  fof(f185,plain,(
% 1.72/0.64    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1) | spl8_12),
% 1.72/0.64    inference(resolution,[],[f104,f173])).
% 1.72/0.64  fof(f173,plain,(
% 1.72/0.64    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_12),
% 1.72/0.64    inference(avatar_component_clause,[],[f171])).
% 1.72/0.64  fof(f104,plain,(
% 1.72/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f34])).
% 1.72/0.64  fof(f34,plain,(
% 1.72/0.64    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.72/0.64    inference(flattening,[],[f33])).
% 1.72/0.64  fof(f33,plain,(
% 1.72/0.64    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.72/0.64    inference(ennf_transformation,[],[f6])).
% 1.72/0.64  fof(f6,axiom,(
% 1.72/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.72/0.64  fof(f182,plain,(
% 1.72/0.64    spl8_13 | ~spl8_6),
% 1.72/0.64    inference(avatar_split_clause,[],[f177,f142,f179])).
% 1.72/0.64  fof(f177,plain,(
% 1.72/0.64    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_6),
% 1.72/0.64    inference(resolution,[],[f82,f144])).
% 1.72/0.64  fof(f82,plain,(
% 1.72/0.64    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.72/0.64    inference(cnf_transformation,[],[f22])).
% 1.72/0.64  fof(f22,plain,(
% 1.72/0.64    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.72/0.64    inference(ennf_transformation,[],[f10])).
% 1.72/0.64  fof(f10,axiom,(
% 1.72/0.64    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.72/0.64  fof(f176,plain,(
% 1.72/0.64    ~spl8_11 | spl8_12),
% 1.72/0.64    inference(avatar_split_clause,[],[f175,f171,f167])).
% 1.72/0.64  fof(f175,plain,(
% 1.72/0.64    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_12),
% 1.72/0.64    inference(subsumption_resolution,[],[f79,f173])).
% 1.72/0.64  fof(f79,plain,(
% 1.72/0.64    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f46,plain,(
% 1.72/0.64    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.72/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 1.72/0.64  fof(f44,plain,(
% 1.72/0.64    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f45,plain,(
% 1.72/0.64    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.72/0.64    introduced(choice_axiom,[])).
% 1.72/0.64  fof(f43,plain,(
% 1.72/0.64    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.72/0.64    inference(flattening,[],[f42])).
% 1.72/0.64  fof(f42,plain,(
% 1.72/0.64    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.72/0.64    inference(nnf_transformation,[],[f20])).
% 1.72/0.64  fof(f20,plain,(
% 1.72/0.64    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.72/0.64    inference(flattening,[],[f19])).
% 1.72/0.64  fof(f19,plain,(
% 1.72/0.64    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.72/0.64    inference(ennf_transformation,[],[f18])).
% 1.72/0.64  fof(f18,negated_conjecture,(
% 1.72/0.64    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.72/0.64    inference(negated_conjecture,[],[f17])).
% 1.72/0.64  fof(f17,conjecture,(
% 1.72/0.64    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.72/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.72/0.64  fof(f174,plain,(
% 1.72/0.64    spl8_11 | ~spl8_12),
% 1.72/0.64    inference(avatar_split_clause,[],[f78,f171,f167])).
% 1.72/0.64  fof(f78,plain,(
% 1.72/0.64    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f165,plain,(
% 1.72/0.64    spl8_10),
% 1.72/0.64    inference(avatar_split_clause,[],[f77,f162])).
% 1.72/0.64  fof(f77,plain,(
% 1.72/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f160,plain,(
% 1.72/0.64    spl8_9),
% 1.72/0.64    inference(avatar_split_clause,[],[f76,f157])).
% 1.72/0.64  fof(f76,plain,(
% 1.72/0.64    v13_waybel_0(sK1,sK0)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f150,plain,(
% 1.72/0.64    ~spl8_7),
% 1.72/0.64    inference(avatar_split_clause,[],[f74,f147])).
% 1.72/0.64  fof(f74,plain,(
% 1.72/0.64    ~v1_xboole_0(sK1)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f145,plain,(
% 1.72/0.64    spl8_6),
% 1.72/0.64    inference(avatar_split_clause,[],[f73,f142])).
% 1.72/0.64  fof(f73,plain,(
% 1.72/0.64    l1_orders_2(sK0)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f140,plain,(
% 1.72/0.64    spl8_5),
% 1.72/0.64    inference(avatar_split_clause,[],[f72,f137])).
% 1.72/0.64  fof(f72,plain,(
% 1.72/0.64    v1_yellow_0(sK0)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f135,plain,(
% 1.72/0.64    spl8_4),
% 1.72/0.64    inference(avatar_split_clause,[],[f71,f132])).
% 1.72/0.64  fof(f71,plain,(
% 1.72/0.64    v5_orders_2(sK0)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  fof(f120,plain,(
% 1.72/0.64    ~spl8_1),
% 1.72/0.64    inference(avatar_split_clause,[],[f68,f117])).
% 1.72/0.64  fof(f68,plain,(
% 1.72/0.64    ~v2_struct_0(sK0)),
% 1.72/0.64    inference(cnf_transformation,[],[f46])).
% 1.72/0.64  % SZS output end Proof for theBenchmark
% 1.72/0.64  % (3585)------------------------------
% 1.72/0.64  % (3585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.64  % (3585)Termination reason: Refutation
% 1.72/0.64  
% 1.72/0.64  % (3585)Memory used [KB]: 6908
% 1.72/0.64  % (3585)Time elapsed: 0.177 s
% 1.72/0.64  % (3585)------------------------------
% 1.72/0.64  % (3585)------------------------------
% 1.72/0.64  % (3581)Success in time 0.278 s
%------------------------------------------------------------------------------
