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
% DateTime   : Thu Dec  3 13:17:17 EST 2020

% Result     : Theorem 11.33s
% Output     : Refutation 11.33s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 609 expanded)
%              Number of leaves         :   55 ( 251 expanded)
%              Depth                    :   24
%              Number of atoms          : 1185 (4286 expanded)
%              Number of equality atoms :   92 ( 510 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f136,f141,f151,f161,f166,f171,f631,f711,f732,f779,f784,f789,f893,f915,f920,f925,f1608,f1747,f5835,f6118,f6143,f12357,f22380,f22404,f22512,f33684,f33688,f33736])).

fof(f33736,plain,
    ( ~ spl15_3
    | ~ spl15_5
    | ~ spl15_51
    | spl15_72
    | ~ spl15_76
    | ~ spl15_814 ),
    inference(avatar_contradiction_clause,[],[f33735])).

fof(f33735,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_51
    | spl15_72
    | ~ spl15_76
    | ~ spl15_814 ),
    inference(subsumption_resolution,[],[f33702,f788])).

fof(f788,plain,
    ( ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11))
    | spl15_72 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl15_72
  <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f33702,plain,
    ( r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11))
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_76
    | ~ spl15_814 ),
    inference(unit_resulting_resolution,[],[f8589,f23164])).

fof(f23164,plain,
    ( ! [X15] :
        ( r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11))
        | ~ r2_hidden(X15,sK11) )
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_76 ),
    inference(subsumption_resolution,[],[f23163,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK9))
        | ~ r2_hidden(X0,sK11) )
    | ~ spl15_3 ),
    inference(resolution,[],[f125,f140])).

fof(f140,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl15_3
  <=> m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f23163,plain,
    ( ! [X15] :
        ( ~ r2_hidden(X15,sK11)
        | ~ m1_subset_1(X15,u1_struct_0(sK9))
        | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11)) )
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_76 ),
    inference(subsumption_resolution,[],[f23162,f150])).

fof(f150,plain,
    ( l1_orders_2(sK9)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl15_5
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f23162,plain,
    ( ! [X15] :
        ( ~ l1_orders_2(sK9)
        | ~ r2_hidden(X15,sK11)
        | ~ m1_subset_1(X15,u1_struct_0(sK9))
        | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11)) )
    | ~ spl15_51
    | ~ spl15_76 ),
    inference(subsumption_resolution,[],[f23133,f630])).

fof(f630,plain,
    ( m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9))
    | ~ spl15_51 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl15_51
  <=> m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).

fof(f23133,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9))
        | ~ l1_orders_2(sK9)
        | ~ r2_hidden(X15,sK11)
        | ~ m1_subset_1(X15,u1_struct_0(sK9))
        | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11)) )
    | ~ spl15_76 ),
    inference(resolution,[],[f807,f1021])).

fof(f1021,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2) ) ),
    inference(resolution,[],[f262,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK13(X0,X1,X2),X0)
          & r2_hidden(sK13(X0,X1,X2),X2)
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK13(X0,X1,X2),X0)
        & r2_hidden(sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ( sP5(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X3,X2)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f110,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP6(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f23,f40,f39])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( r2_lattice3(X0,X1,X2)
      <=> sP5(X2,X0,X1) )
      | ~ sP6(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP5(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_lattice3(X1,X0,X2)
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_lattice3(X1,X0,X2) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_lattice3(X0,X1,X2)
          | ~ sP5(X2,X0,X1) )
        & ( sP5(X2,X0,X1)
          | ~ r2_lattice3(X0,X1,X2) ) )
      | ~ sP6(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f807,plain,
    ( r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11))
    | ~ spl15_76 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl15_76
  <=> r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).

fof(f8589,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)
    | ~ spl15_814 ),
    inference(avatar_component_clause,[],[f8588])).

fof(f8588,plain,
    ( spl15_814
  <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_814])])).

fof(f33688,plain,
    ( spl15_3232
    | spl15_814
    | ~ spl15_5
    | ~ spl15_71
    | ~ spl15_153
    | ~ spl15_561
    | ~ spl15_572 ),
    inference(avatar_split_clause,[],[f33687,f6140,f6084,f1605,f781,f148,f8588,f33596])).

fof(f33596,plain,
    ( spl15_3232
  <=> k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3232])])).

fof(f781,plain,
    ( spl15_71
  <=> m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_71])])).

fof(f1605,plain,
    ( spl15_153
  <=> m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_153])])).

fof(f6084,plain,
    ( spl15_561
  <=> sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_561])])).

fof(f6140,plain,
    ( spl15_572
  <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_572])])).

fof(f33687,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)
    | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ spl15_5
    | ~ spl15_71
    | ~ spl15_153
    | ~ spl15_561
    | ~ spl15_572 ),
    inference(subsumption_resolution,[],[f33686,f6086])).

fof(f6086,plain,
    ( sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)
    | ~ spl15_561 ),
    inference(avatar_component_clause,[],[f6084])).

fof(f33686,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)
    | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)
    | ~ spl15_5
    | ~ spl15_71
    | ~ spl15_153
    | ~ spl15_572 ),
    inference(subsumption_resolution,[],[f33685,f6142])).

fof(f6142,plain,
    ( r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ spl15_572 ),
    inference(avatar_component_clause,[],[f6140])).

fof(f33685,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)
    | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)
    | ~ spl15_5
    | ~ spl15_71
    | ~ spl15_153 ),
    inference(subsumption_resolution,[],[f33586,f783])).

fof(f783,plain,
    ( m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9))
    | ~ spl15_71 ),
    inference(avatar_component_clause,[],[f781])).

fof(f33586,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)
    | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)
    | ~ spl15_5
    | ~ spl15_153 ),
    inference(resolution,[],[f1607,f8816])).

fof(f8816,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10))
        | r2_hidden(X0,sK11)
        | k1_xboole_0 = k1_tarski(X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ r1_orders_2(sK9,X0,X0)
        | ~ sP1(X0,X0,sK9) )
    | ~ spl15_5 ),
    inference(resolution,[],[f4613,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X2,k1_tarski(X1),X0)
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_lattice3(X2,k1_tarski(X1),X0)
          | ~ r1_orders_2(X2,X1,X0) )
        & ( r1_orders_2(X2,X1,X0)
          | ~ r2_lattice3(X2,k1_tarski(X1),X0) )
        & ( r1_lattice3(X2,k1_tarski(X1),X0)
          | ~ r1_orders_2(X2,X0,X1) )
        & ( r1_orders_2(X2,X0,X1)
          | ~ r1_lattice3(X2,k1_tarski(X1),X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
          | ~ r1_orders_2(X0,X2,X1) )
        & ( r1_orders_2(X0,X2,X1)
          | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
        & ( r1_lattice3(X0,k1_tarski(X2),X1)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
          | ~ r1_orders_2(X0,X2,X1) )
        & ( r1_orders_2(X0,X2,X1)
          | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
        & ( r1_lattice3(X0,k1_tarski(X2),X1)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4613,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK9,k1_tarski(X0),X0)
        | k1_xboole_0 = k1_tarski(X0)
        | r2_hidden(X0,sK11)
        | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9)) )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f4612,f92])).

fof(f92,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f4612,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ v1_finset_1(k1_tarski(X0))
        | k1_xboole_0 = k1_tarski(X0)
        | r2_hidden(X0,sK11)
        | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10))
        | ~ r2_lattice3(sK9,k1_tarski(X0),X0) )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f4591,f150])).

fof(f4591,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ l1_orders_2(sK9)
        | ~ v1_finset_1(k1_tarski(X0))
        | k1_xboole_0 = k1_tarski(X0)
        | r2_hidden(X0,sK11)
        | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10))
        | ~ r2_lattice3(sK9,k1_tarski(X0),X0) )
    | ~ spl15_5 ),
    inference(duplicate_literal_removal,[],[f4588])).

fof(f4588,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ l1_orders_2(sK9)
        | ~ v1_finset_1(k1_tarski(X0))
        | k1_xboole_0 = k1_tarski(X0)
        | r2_hidden(X0,sK11)
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10))
        | ~ r2_lattice3(sK9,k1_tarski(X0),X0) )
    | ~ spl15_5 ),
    inference(resolution,[],[f2234,f1748])).

fof(f1748,plain,
    ( ! [X0,X1] :
        ( ~ sP2(X1,sK9,X0)
        | ~ v1_finset_1(X0)
        | k1_xboole_0 = X0
        | r2_hidden(X1,sK11)
        | ~ m1_subset_1(X1,u1_struct_0(sK9))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
        | ~ r2_lattice3(sK9,X0,X1) )
    | ~ spl15_5 ),
    inference(resolution,[],[f906,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | ~ r2_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ sP2(X2,X1,X0)
        | ~ r2_lattice3(X1,X0,X2) )
      & ( ( sP2(X2,X1,X0)
          & r2_lattice3(X1,X0,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( sP2(X2,X0,X1)
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f906,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK9,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
        | ~ v1_finset_1(X0)
        | k1_xboole_0 = X0
        | r2_hidden(X1,sK11)
        | ~ m1_subset_1(X1,u1_struct_0(sK9)) )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f905,f85])).

fof(f85,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(sK10))
      | k1_xboole_0 = X5
      | r1_yellow_0(sK9,X5)
      | ~ v1_finset_1(X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11)
    & r1_yellow_0(sK9,sK10)
    & ! [X3] :
        ( r2_hidden(k1_yellow_0(sK9,X3),sK11)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( sP0(X4,sK9,sK10)
        | ~ r2_hidden(X4,sK11)
        | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
    & ! [X5] :
        ( r1_yellow_0(sK9,X5)
        | k1_xboole_0 = X5
        | ~ m1_subset_1(X5,k1_zfmisc_1(sK10))
        | ~ v1_finset_1(X5) )
    & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))
    & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    & l1_orders_2(sK9)
    & v4_orders_2(sK9)
    & v3_orders_2(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f48,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
                & r1_yellow_0(X0,X1)
                & ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,X3),X2)
                    | k1_xboole_0 = X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X3) )
                & ! [X4] :
                    ( sP0(X4,X0,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_yellow_0(X0,X5)
                    | k1_xboole_0 = X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X5) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(sK9,X1) != k1_yellow_0(sK9,X2)
              & r1_yellow_0(sK9,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(sK9,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( sP0(X4,sK9,X1)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
              & ! [X5] :
                  ( r1_yellow_0(sK9,X5)
                  | k1_xboole_0 = X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X5) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9))) )
      & l1_orders_2(sK9)
      & v4_orders_2(sK9)
      & v3_orders_2(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_yellow_0(sK9,X1) != k1_yellow_0(sK9,X2)
            & r1_yellow_0(sK9,X1)
            & ! [X3] :
                ( r2_hidden(k1_yellow_0(sK9,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( sP0(X4,sK9,X1)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
            & ! [X5] :
                ( r1_yellow_0(sK9,X5)
                | k1_xboole_0 = X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X5) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9))) )
   => ( ? [X2] :
          ( k1_yellow_0(sK9,X2) != k1_yellow_0(sK9,sK10)
          & r1_yellow_0(sK9,sK10)
          & ! [X3] :
              ( r2_hidden(k1_yellow_0(sK9,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( sP0(X4,sK9,sK10)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
          & ! [X5] :
              ( r1_yellow_0(sK9,X5)
              | k1_xboole_0 = X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(sK10))
              | ~ v1_finset_1(X5) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) )
      & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( k1_yellow_0(sK9,X2) != k1_yellow_0(sK9,sK10)
        & r1_yellow_0(sK9,sK10)
        & ! [X3] :
            ( r2_hidden(k1_yellow_0(sK9,X3),X2)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( sP0(X4,sK9,sK10)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
        & ! [X5] :
            ( r1_yellow_0(sK9,X5)
            | k1_xboole_0 = X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(sK10))
            | ~ v1_finset_1(X5) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) )
   => ( k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11)
      & r1_yellow_0(sK9,sK10)
      & ! [X3] :
          ( r2_hidden(k1_yellow_0(sK9,X3),sK11)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
          | ~ v1_finset_1(X3) )
      & ! [X4] :
          ( sP0(X4,sK9,sK10)
          | ~ r2_hidden(X4,sK11)
          | ~ m1_subset_1(X4,u1_struct_0(sK9)) )
      & ! [X5] :
          ( r1_yellow_0(sK9,X5)
          | k1_xboole_0 = X5
          | ~ m1_subset_1(X5,k1_zfmisc_1(sK10))
          | ~ v1_finset_1(X5) )
      & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( sP0(X4,X0,X1)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_yellow_0(X0,X5)
                  | k1_xboole_0 = X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X5) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( sP0(X4,X0,X1)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ? [X5] :
          ( k1_yellow_0(X0,X5) = X4
          & r1_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
      | ~ sP0(X4,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_yellow_0(X0,X1)
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_waybel_0)).

fof(f905,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
        | ~ v1_finset_1(X0)
        | ~ sP3(X0,sK9,X1)
        | r2_hidden(X1,sK11)
        | ~ r1_yellow_0(sK9,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK9)) )
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f903,f150])).

fof(f903,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
      | ~ v1_finset_1(X0)
      | ~ sP3(X0,sK9,X1)
      | r2_hidden(X1,sK11)
      | ~ r1_yellow_0(sK9,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK9))
      | ~ l1_orders_2(sK9) ) ),
    inference(resolution,[],[f275,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X2,X0,X1)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f21,f37,f36,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f275,plain,(
    ! [X2,X1] :
      ( ~ sP4(X2,sK9,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK10))
      | ~ v1_finset_1(X1)
      | ~ sP3(X1,sK9,X2)
      | r2_hidden(X2,sK11) ) ),
    inference(superposition,[],[f87,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X1,X2) = X0
      | ~ sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X2) = X0
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k1_yellow_0(X1,X2) != X0 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK9,X3),sK11)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2234,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1,k1_tarski(X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f2233])).

fof(f2233,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1,k1_tarski(X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,k1_tarski(X0)) ) ),
    inference(resolution,[],[f1381,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
          & r2_lattice3(X1,X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
        & r2_lattice3(X1,X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f1381,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1)))
      | sP2(X2,X0,k1_tarski(X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1380,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1380,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1)))
      | sP2(X2,X0,k1_tarski(X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK12(X2,X0,k1_tarski(X1)),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f268,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f33])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(sK12(X2,X0,k1_tarski(X1)),X1,X0)
      | r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1)))
      | sP2(X2,X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f95,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK12(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X2,k1_tarski(X1),X0)
      | r1_orders_2(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1607,plain,
    ( m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10))
    | ~ spl15_153 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f33684,plain,
    ( ~ spl15_9
    | ~ spl15_3232 ),
    inference(avatar_contradiction_clause,[],[f33683])).

fof(f33683,plain,
    ( $false
    | ~ spl15_9
    | ~ spl15_3232 ),
    inference(subsumption_resolution,[],[f33631,f170])).

fof(f170,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl15_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f33631,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl15_3232 ),
    inference(superposition,[],[f91,f33598])).

fof(f33598,plain,
    ( k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ spl15_3232 ),
    inference(avatar_component_clause,[],[f33596])).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f22512,plain,
    ( ~ spl15_1190
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_88
    | spl15_89
    | ~ spl15_168 ),
    inference(avatar_split_clause,[],[f21840,f1744,f922,f917,f628,f148,f12354])).

fof(f12354,plain,
    ( spl15_1190
  <=> r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1190])])).

fof(f917,plain,
    ( spl15_88
  <=> m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_88])])).

fof(f922,plain,
    ( spl15_89
  <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_89])])).

fof(f1744,plain,
    ( spl15_168
  <=> sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_168])])).

fof(f21840,plain,
    ( ~ r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11))
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_88
    | spl15_89
    | ~ spl15_168 ),
    inference(unit_resulting_resolution,[],[f150,f630,f1746,f919,f924,f4772])).

fof(f4772,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_lattice3(X2,sK8(X3,X2,X4),X5)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ sP0(X3,X2,X4)
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | r1_orders_2(X2,X3,X5) ) ),
    inference(resolution,[],[f2004,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2004,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,sK8(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP0(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f2001,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,sK8(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k1_yellow_0(X1,sK8(X0,X1,X2)) = X0
        & r1_yellow_0(X1,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK8(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X1,X3) = X0
          & r1_yellow_0(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( k1_yellow_0(X1,sK8(X0,X1,X2)) = X0
        & r1_yellow_0(X1,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k1_yellow_0(X1,X3) = X0
          & r1_yellow_0(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ? [X5] :
          ( k1_yellow_0(X0,X5) = X4
          & r1_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
      | ~ sP0(X4,X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f2001,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,sK8(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,sK8(X1,X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP0(X1,X0,X2) ) ),
    inference(superposition,[],[f1149,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X1,sK8(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1149,plain,(
    ! [X0,X1] :
      ( sP2(k1_yellow_0(X0,X1),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f303,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f303,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0,k1_yellow_0(X0,X1))
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f109,f126])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ sP4(k1_yellow_0(X1,X2),X1,X2)
      | sP3(X2,X1,k1_yellow_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k1_yellow_0(X1,X2) != X0
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f924,plain,
    ( ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11))
    | spl15_89 ),
    inference(avatar_component_clause,[],[f922])).

fof(f919,plain,
    ( m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9))
    | ~ spl15_88 ),
    inference(avatar_component_clause,[],[f917])).

fof(f1746,plain,
    ( sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10)
    | ~ spl15_168 ),
    inference(avatar_component_clause,[],[f1744])).

fof(f22404,plain,
    ( ~ spl15_76
    | ~ spl15_62
    | ~ spl15_61 ),
    inference(avatar_split_clause,[],[f3466,f708,f714,f806])).

fof(f714,plain,
    ( spl15_62
  <=> r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).

fof(f708,plain,
    ( spl15_61
  <=> sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_61])])).

fof(f3466,plain,
    ( ~ r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11))
    | ~ r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11))
    | ~ spl15_61 ),
    inference(resolution,[],[f710,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X0,X1,X2,X3)
      | ~ r2_lattice3(X2,X3,X0)
      | ~ r2_lattice3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ r2_lattice3(X2,X1,X0)
          | ~ r2_lattice3(X2,X3,X0) )
        & ( r2_lattice3(X2,X1,X0)
          | r2_lattice3(X2,X3,X0) ) )
      | ~ sP7(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( ~ r2_lattice3(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3) )
        & ( r2_lattice3(X0,X2,X3)
          | r2_lattice3(X0,X1,X3) ) )
      | ~ sP7(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X3,X2,X0,X1] :
      ( ( r2_lattice3(X0,X1,X3)
      <~> r2_lattice3(X0,X2,X3) )
      | ~ sP7(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f710,plain,
    ( sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10)
    | ~ spl15_61 ),
    inference(avatar_component_clause,[],[f708])).

fof(f22380,plain,
    ( spl15_76
    | spl15_62
    | ~ spl15_61 ),
    inference(avatar_split_clause,[],[f3467,f708,f714,f806])).

fof(f3467,plain,
    ( r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11))
    | r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11))
    | ~ spl15_61 ),
    inference(resolution,[],[f710,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X0,X1,X2,X3)
      | r2_lattice3(X2,X3,X0)
      | r2_lattice3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f12357,plain,
    ( spl15_1190
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_62
    | ~ spl15_531 ),
    inference(avatar_split_clause,[],[f12322,f5832,f714,f628,f148,f12354])).

fof(f5832,plain,
    ( spl15_531
  <=> r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_531])])).

fof(f12322,plain,
    ( r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11))
    | ~ spl15_5
    | ~ spl15_51
    | ~ spl15_62
    | ~ spl15_531 ),
    inference(unit_resulting_resolution,[],[f150,f715,f630,f5834,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f5834,plain,
    ( r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10)
    | ~ spl15_531 ),
    inference(avatar_component_clause,[],[f5832])).

fof(f715,plain,
    ( r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11))
    | ~ spl15_62 ),
    inference(avatar_component_clause,[],[f714])).

fof(f6143,plain,
    ( spl15_572
    | ~ spl15_5
    | ~ spl15_7
    | spl15_8
    | ~ spl15_71 ),
    inference(avatar_split_clause,[],[f6016,f781,f163,f158,f148,f6140])).

fof(f158,plain,
    ( spl15_7
  <=> v3_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f163,plain,
    ( spl15_8
  <=> v2_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f6016,plain,
    ( r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10))
    | ~ spl15_5
    | ~ spl15_7
    | spl15_8
    | ~ spl15_71 ),
    inference(unit_resulting_resolution,[],[f165,f160,f150,f783,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f160,plain,
    ( v3_orders_2(sK9)
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f165,plain,
    ( ~ v2_struct_0(sK9)
    | spl15_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f6118,plain,
    ( spl15_561
    | ~ spl15_5
    | ~ spl15_71 ),
    inference(avatar_split_clause,[],[f6006,f781,f148,f6084])).

fof(f6006,plain,
    ( sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)
    | ~ spl15_5
    | ~ spl15_71 ),
    inference(unit_resulting_resolution,[],[f150,f783,f783,f97])).

fof(f5835,plain,
    ( spl15_531
    | ~ spl15_168 ),
    inference(avatar_split_clause,[],[f5808,f1744,f5832])).

fof(f5808,plain,
    ( r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10)
    | ~ spl15_168 ),
    inference(unit_resulting_resolution,[],[f1746,f205])).

fof(f205,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(sK8(X6,X7,X8),X8)
      | ~ sP0(X6,X7,X8) ) ),
    inference(resolution,[],[f76,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1747,plain,
    ( spl15_168
    | ~ spl15_87
    | ~ spl15_88 ),
    inference(avatar_split_clause,[],[f1708,f917,f912,f1744])).

fof(f912,plain,
    ( spl15_87
  <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_87])])).

fof(f1708,plain,
    ( sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10)
    | ~ spl15_87
    | ~ spl15_88 ),
    inference(unit_resulting_resolution,[],[f914,f919,f86])).

fof(f86,plain,(
    ! [X4] :
      ( sP0(X4,sK9,sK10)
      | ~ r2_hidden(X4,sK11)
      | ~ m1_subset_1(X4,u1_struct_0(sK9)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f914,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11)
    | ~ spl15_87 ),
    inference(avatar_component_clause,[],[f912])).

fof(f1608,plain,
    ( spl15_153
    | ~ spl15_70 ),
    inference(avatar_split_clause,[],[f1603,f776,f1605])).

fof(f776,plain,
    ( spl15_70
  <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f1603,plain,
    ( m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10))
    | ~ spl15_70 ),
    inference(unit_resulting_resolution,[],[f778,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f778,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10)
    | ~ spl15_70 ),
    inference(avatar_component_clause,[],[f776])).

fof(f925,plain,
    ( ~ spl15_89
    | spl15_85 ),
    inference(avatar_split_clause,[],[f908,f890,f922])).

fof(f890,plain,
    ( spl15_85
  <=> sP5(sK14(sK9,sK10,sK11),sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_85])])).

fof(f908,plain,
    ( ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11))
    | spl15_85 ),
    inference(unit_resulting_resolution,[],[f892,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK13(X0,X1,X2),X0)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f892,plain,
    ( ~ sP5(sK14(sK9,sK10,sK11),sK9,sK11)
    | spl15_85 ),
    inference(avatar_component_clause,[],[f890])).

fof(f920,plain,
    ( spl15_88
    | spl15_85 ),
    inference(avatar_split_clause,[],[f909,f890,f917])).

fof(f909,plain,
    ( m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9))
    | spl15_85 ),
    inference(unit_resulting_resolution,[],[f892,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f915,plain,
    ( spl15_87
    | spl15_85 ),
    inference(avatar_split_clause,[],[f910,f890,f912])).

fof(f910,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11)
    | spl15_85 ),
    inference(unit_resulting_resolution,[],[f892,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X2)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f893,plain,
    ( ~ spl15_85
    | ~ spl15_5
    | ~ spl15_51
    | spl15_76 ),
    inference(avatar_split_clause,[],[f886,f806,f628,f148,f890])).

fof(f886,plain,
    ( ~ sP5(sK14(sK9,sK10,sK11),sK9,sK11)
    | ~ spl15_5
    | ~ spl15_51
    | spl15_76 ),
    inference(unit_resulting_resolution,[],[f637,f808,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ sP5(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f808,plain,
    ( ~ r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11))
    | spl15_76 ),
    inference(avatar_component_clause,[],[f806])).

fof(f637,plain,
    ( ! [X0] : sP6(X0,sK9,sK14(sK9,sK10,sK11))
    | ~ spl15_5
    | ~ spl15_51 ),
    inference(unit_resulting_resolution,[],[f150,f630,f116])).

fof(f789,plain,
    ( ~ spl15_72
    | spl15_64 ),
    inference(avatar_split_clause,[],[f772,f729,f786])).

fof(f729,plain,
    ( spl15_64
  <=> sP5(sK14(sK9,sK10,sK11),sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f772,plain,
    ( ~ r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11))
    | spl15_64 ),
    inference(unit_resulting_resolution,[],[f731,f115])).

fof(f731,plain,
    ( ~ sP5(sK14(sK9,sK10,sK11),sK9,sK10)
    | spl15_64 ),
    inference(avatar_component_clause,[],[f729])).

fof(f784,plain,
    ( spl15_71
    | spl15_64 ),
    inference(avatar_split_clause,[],[f773,f729,f781])).

fof(f773,plain,
    ( m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9))
    | spl15_64 ),
    inference(unit_resulting_resolution,[],[f731,f113])).

fof(f779,plain,
    ( spl15_70
    | spl15_64 ),
    inference(avatar_split_clause,[],[f774,f729,f776])).

fof(f774,plain,
    ( r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10)
    | spl15_64 ),
    inference(unit_resulting_resolution,[],[f731,f114])).

fof(f732,plain,
    ( ~ spl15_64
    | ~ spl15_5
    | ~ spl15_51
    | spl15_62 ),
    inference(avatar_split_clause,[],[f725,f714,f628,f148,f729])).

fof(f725,plain,
    ( ~ sP5(sK14(sK9,sK10,sK11),sK9,sK10)
    | ~ spl15_5
    | ~ spl15_51
    | spl15_62 ),
    inference(unit_resulting_resolution,[],[f637,f716,f111])).

fof(f716,plain,
    ( ~ r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11))
    | spl15_62 ),
    inference(avatar_component_clause,[],[f714])).

fof(f711,plain,
    ( spl15_61
    | spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_8 ),
    inference(avatar_split_clause,[],[f703,f163,f148,f133,f128,f708])).

fof(f128,plain,
    ( spl15_1
  <=> k1_yellow_0(sK9,sK10) = k1_yellow_0(sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f133,plain,
    ( spl15_2
  <=> r1_yellow_0(sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f703,plain,
    ( sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10)
    | spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_8 ),
    inference(unit_resulting_resolution,[],[f165,f150,f135,f130,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK14(X0,X1,X2),X2,X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( sP7(sK14(X0,X1,X2),X2,X0,X1)
            & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f43,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP7(X3,X2,X0,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sP7(sK14(X0,X1,X2),X2,X0,X1)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( sP7(X3,X2,X0,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f42])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f130,plain,
    ( k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( r1_yellow_0(sK9,sK10)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f631,plain,
    ( spl15_51
    | spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_8 ),
    inference(avatar_split_clause,[],[f626,f163,f148,f133,f128,f628])).

fof(f626,plain,
    ( m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9))
    | spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_8 ),
    inference(unit_resulting_resolution,[],[f165,f150,f135,f130,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f171,plain,(
    spl15_9 ),
    inference(avatar_split_clause,[],[f90,f168])).

fof(f90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f166,plain,(
    ~ spl15_8 ),
    inference(avatar_split_clause,[],[f79,f163])).

fof(f79,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f161,plain,(
    spl15_7 ),
    inference(avatar_split_clause,[],[f80,f158])).

fof(f80,plain,(
    v3_orders_2(sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f151,plain,(
    spl15_5 ),
    inference(avatar_split_clause,[],[f82,f148])).

fof(f82,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f141,plain,(
    spl15_3 ),
    inference(avatar_split_clause,[],[f84,f138])).

fof(f84,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f88,f133])).

fof(f88,plain,(
    r1_yellow_0(sK9,sK10) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f89,f128])).

fof(f89,plain,(
    k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (22048)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (22061)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (22051)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (22068)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (22060)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (22060)Refutation not found, incomplete strategy% (22060)------------------------------
% 0.21/0.51  % (22060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22060)Memory used [KB]: 10746
% 0.21/0.51  % (22060)Time elapsed: 0.080 s
% 0.21/0.51  % (22060)------------------------------
% 0.21/0.51  % (22060)------------------------------
% 0.21/0.51  % (22050)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (22062)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (22049)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22066)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (22065)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (22058)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (22052)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (22055)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (22054)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (22056)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (22067)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (22057)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (22064)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (22053)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.49/0.54  % (22069)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.49/0.55  % (22063)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.49/0.55  % (22063)Refutation not found, incomplete strategy% (22063)------------------------------
% 1.49/0.55  % (22063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (22063)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (22063)Memory used [KB]: 10746
% 1.49/0.55  % (22063)Time elapsed: 0.142 s
% 1.49/0.55  % (22063)------------------------------
% 1.49/0.55  % (22063)------------------------------
% 3.97/0.91  % (22048)Time limit reached!
% 3.97/0.91  % (22048)------------------------------
% 3.97/0.91  % (22048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.91  % (22048)Termination reason: Time limit
% 3.97/0.91  % (22048)Termination phase: Saturation
% 3.97/0.91  
% 3.97/0.91  % (22048)Memory used [KB]: 9338
% 3.97/0.91  % (22048)Time elapsed: 0.500 s
% 3.97/0.91  % (22048)------------------------------
% 3.97/0.91  % (22048)------------------------------
% 3.97/0.92  % (22058)Time limit reached!
% 3.97/0.92  % (22058)------------------------------
% 3.97/0.92  % (22058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.92  % (22058)Termination reason: Time limit
% 3.97/0.92  
% 3.97/0.92  % (22058)Memory used [KB]: 11001
% 3.97/0.92  % (22058)Time elapsed: 0.510 s
% 3.97/0.92  % (22058)------------------------------
% 3.97/0.92  % (22058)------------------------------
% 4.54/0.93  % (22061)Time limit reached!
% 4.54/0.93  % (22061)------------------------------
% 4.54/0.93  % (22061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.93  % (22061)Termination reason: Time limit
% 4.54/0.93  % (22061)Termination phase: Saturation
% 4.54/0.93  
% 4.54/0.93  % (22061)Memory used [KB]: 10490
% 4.54/0.93  % (22061)Time elapsed: 0.500 s
% 4.54/0.93  % (22061)------------------------------
% 4.54/0.93  % (22061)------------------------------
% 4.54/0.93  % (22053)Time limit reached!
% 4.54/0.93  % (22053)------------------------------
% 4.54/0.93  % (22053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.93  % (22053)Termination reason: Time limit
% 4.54/0.93  
% 4.54/0.93  % (22053)Memory used [KB]: 6780
% 4.54/0.93  % (22053)Time elapsed: 0.517 s
% 4.54/0.93  % (22053)------------------------------
% 4.54/0.93  % (22053)------------------------------
% 4.88/0.96  % (22049)Time limit reached!
% 4.88/0.96  % (22049)------------------------------
% 4.88/0.96  % (22049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/0.96  % (22049)Termination reason: Time limit
% 4.88/0.96  
% 4.88/0.96  % (22049)Memory used [KB]: 13304
% 4.88/0.96  % (22049)Time elapsed: 0.532 s
% 4.88/0.96  % (22049)------------------------------
% 4.88/0.96  % (22049)------------------------------
% 4.88/1.02  % (22069)Time limit reached!
% 4.88/1.02  % (22069)------------------------------
% 4.88/1.02  % (22069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.02  % (22069)Termination reason: Time limit
% 4.88/1.02  
% 4.88/1.02  % (22069)Memory used [KB]: 11641
% 4.88/1.02  % (22069)Time elapsed: 0.609 s
% 4.88/1.02  % (22069)------------------------------
% 4.88/1.02  % (22069)------------------------------
% 5.49/1.06  % (22056)Time limit reached!
% 5.49/1.06  % (22056)------------------------------
% 5.49/1.06  % (22056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.49/1.06  % (22056)Termination reason: Time limit
% 5.49/1.06  
% 5.49/1.06  % (22056)Memory used [KB]: 8827
% 5.49/1.06  % (22056)Time elapsed: 0.627 s
% 5.49/1.06  % (22056)------------------------------
% 5.49/1.06  % (22056)------------------------------
% 7.84/1.33  % (22057)Time limit reached!
% 7.84/1.33  % (22057)------------------------------
% 7.84/1.33  % (22057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.84/1.33  % (22057)Termination reason: Time limit
% 7.84/1.33  % (22057)Termination phase: Saturation
% 7.84/1.33  
% 7.84/1.33  % (22057)Memory used [KB]: 18038
% 7.84/1.33  % (22057)Time elapsed: 0.900 s
% 7.84/1.33  % (22057)------------------------------
% 7.84/1.33  % (22057)------------------------------
% 8.92/1.50  % (22050)Time limit reached!
% 8.92/1.50  % (22050)------------------------------
% 8.92/1.50  % (22050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.92/1.50  % (22050)Termination reason: Time limit
% 8.92/1.50  % (22050)Termination phase: Saturation
% 8.92/1.50  
% 8.92/1.50  % (22050)Memory used [KB]: 15095
% 8.92/1.50  % (22050)Time elapsed: 1.100 s
% 8.92/1.50  % (22050)------------------------------
% 8.92/1.50  % (22050)------------------------------
% 11.18/1.75  % (22051)Time limit reached!
% 11.18/1.75  % (22051)------------------------------
% 11.18/1.75  % (22051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.18/1.75  % (22051)Termination reason: Time limit
% 11.18/1.75  
% 11.18/1.75  % (22051)Memory used [KB]: 18549
% 11.18/1.75  % (22051)Time elapsed: 1.321 s
% 11.18/1.75  % (22051)------------------------------
% 11.18/1.75  % (22051)------------------------------
% 11.33/1.78  % (22065)Refutation found. Thanks to Tanya!
% 11.33/1.78  % SZS status Theorem for theBenchmark
% 11.33/1.78  % SZS output start Proof for theBenchmark
% 11.33/1.78  fof(f33737,plain,(
% 11.33/1.78    $false),
% 11.33/1.78    inference(avatar_sat_refutation,[],[f131,f136,f141,f151,f161,f166,f171,f631,f711,f732,f779,f784,f789,f893,f915,f920,f925,f1608,f1747,f5835,f6118,f6143,f12357,f22380,f22404,f22512,f33684,f33688,f33736])).
% 11.33/1.78  fof(f33736,plain,(
% 11.33/1.78    ~spl15_3 | ~spl15_5 | ~spl15_51 | spl15_72 | ~spl15_76 | ~spl15_814),
% 11.33/1.78    inference(avatar_contradiction_clause,[],[f33735])).
% 11.33/1.78  fof(f33735,plain,(
% 11.33/1.78    $false | (~spl15_3 | ~spl15_5 | ~spl15_51 | spl15_72 | ~spl15_76 | ~spl15_814)),
% 11.33/1.78    inference(subsumption_resolution,[],[f33702,f788])).
% 11.33/1.78  fof(f788,plain,(
% 11.33/1.78    ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) | spl15_72),
% 11.33/1.78    inference(avatar_component_clause,[],[f786])).
% 11.33/1.78  fof(f786,plain,(
% 11.33/1.78    spl15_72 <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).
% 11.33/1.78  fof(f33702,plain,(
% 11.33/1.78    r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) | (~spl15_3 | ~spl15_5 | ~spl15_51 | ~spl15_76 | ~spl15_814)),
% 11.33/1.78    inference(unit_resulting_resolution,[],[f8589,f23164])).
% 11.33/1.78  fof(f23164,plain,(
% 11.33/1.78    ( ! [X15] : (r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11)) | ~r2_hidden(X15,sK11)) ) | (~spl15_3 | ~spl15_5 | ~spl15_51 | ~spl15_76)),
% 11.33/1.78    inference(subsumption_resolution,[],[f23163,f195])).
% 11.33/1.78  fof(f195,plain,(
% 11.33/1.78    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11)) ) | ~spl15_3),
% 11.33/1.78    inference(resolution,[],[f125,f140])).
% 11.33/1.78  fof(f140,plain,(
% 11.33/1.78    m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) | ~spl15_3),
% 11.33/1.78    inference(avatar_component_clause,[],[f138])).
% 11.33/1.78  fof(f138,plain,(
% 11.33/1.78    spl15_3 <=> m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).
% 11.33/1.78  fof(f125,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f30])).
% 11.33/1.78  fof(f30,plain,(
% 11.33/1.78    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.33/1.78    inference(flattening,[],[f29])).
% 11.33/1.78  fof(f29,plain,(
% 11.33/1.78    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.33/1.78    inference(ennf_transformation,[],[f5])).
% 11.33/1.78  fof(f5,axiom,(
% 11.33/1.78    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.33/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 11.33/1.78  fof(f23163,plain,(
% 11.33/1.78    ( ! [X15] : (~r2_hidden(X15,sK11) | ~m1_subset_1(X15,u1_struct_0(sK9)) | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11))) ) | (~spl15_5 | ~spl15_51 | ~spl15_76)),
% 11.33/1.78    inference(subsumption_resolution,[],[f23162,f150])).
% 11.33/1.78  fof(f150,plain,(
% 11.33/1.78    l1_orders_2(sK9) | ~spl15_5),
% 11.33/1.78    inference(avatar_component_clause,[],[f148])).
% 11.33/1.78  fof(f148,plain,(
% 11.33/1.78    spl15_5 <=> l1_orders_2(sK9)),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 11.33/1.78  fof(f23162,plain,(
% 11.33/1.78    ( ! [X15] : (~l1_orders_2(sK9) | ~r2_hidden(X15,sK11) | ~m1_subset_1(X15,u1_struct_0(sK9)) | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11))) ) | (~spl15_51 | ~spl15_76)),
% 11.33/1.78    inference(subsumption_resolution,[],[f23133,f630])).
% 11.33/1.78  fof(f630,plain,(
% 11.33/1.78    m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9)) | ~spl15_51),
% 11.33/1.78    inference(avatar_component_clause,[],[f628])).
% 11.33/1.78  fof(f628,plain,(
% 11.33/1.78    spl15_51 <=> m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).
% 11.33/1.78  fof(f23133,plain,(
% 11.33/1.78    ( ! [X15] : (~m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9)) | ~l1_orders_2(sK9) | ~r2_hidden(X15,sK11) | ~m1_subset_1(X15,u1_struct_0(sK9)) | r1_orders_2(sK9,X15,sK14(sK9,sK10,sK11))) ) | ~spl15_76),
% 11.33/1.78    inference(resolution,[],[f807,f1021])).
% 11.33/1.78  fof(f1021,plain,(
% 11.33/1.78    ( ! [X2,X0,X3,X1] : (~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,X2)) )),
% 11.33/1.78    inference(resolution,[],[f262,f112])).
% 11.33/1.78  fof(f112,plain,(
% 11.33/1.78    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f69])).
% 11.33/1.78  fof(f69,plain,(
% 11.33/1.78    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_orders_2(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 11.33/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f67,f68])).
% 11.33/1.78  fof(f68,plain,(
% 11.33/1.78    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 11.33/1.78    introduced(choice_axiom,[])).
% 11.33/1.78  fof(f67,plain,(
% 11.33/1.78    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 11.33/1.78    inference(rectify,[],[f66])).
% 11.33/1.78  fof(f66,plain,(
% 11.33/1.78    ! [X2,X0,X1] : ((sP5(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X2,X0,X1)))),
% 11.33/1.78    inference(nnf_transformation,[],[f39])).
% 11.33/1.78  fof(f39,plain,(
% 11.33/1.78    ! [X2,X0,X1] : (sP5(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 11.33/1.78    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 11.33/1.78  fof(f262,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.78    inference(resolution,[],[f110,f116])).
% 11.33/1.78  fof(f116,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (sP6(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f41])).
% 11.33/1.78  fof(f41,plain,(
% 11.33/1.78    ! [X0] : (! [X1,X2] : (sP6(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.78    inference(definition_folding,[],[f23,f40,f39])).
% 11.33/1.78  fof(f40,plain,(
% 11.33/1.78    ! [X1,X0,X2] : ((r2_lattice3(X0,X1,X2) <=> sP5(X2,X0,X1)) | ~sP6(X1,X0,X2))),
% 11.33/1.78    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 11.33/1.78  fof(f23,plain,(
% 11.33/1.78    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.78    inference(flattening,[],[f22])).
% 11.33/1.78  fof(f22,plain,(
% 11.33/1.78    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.78    inference(ennf_transformation,[],[f8])).
% 11.33/1.78  fof(f8,axiom,(
% 11.33/1.78    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 11.33/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 11.33/1.78  fof(f110,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (~sP6(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP5(X2,X1,X0)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f65])).
% 11.33/1.78  fof(f65,plain,(
% 11.33/1.78    ! [X0,X1,X2] : (((r2_lattice3(X1,X0,X2) | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | ~r2_lattice3(X1,X0,X2))) | ~sP6(X0,X1,X2))),
% 11.33/1.78    inference(rectify,[],[f64])).
% 11.33/1.78  fof(f64,plain,(
% 11.33/1.78    ! [X1,X0,X2] : (((r2_lattice3(X0,X1,X2) | ~sP5(X2,X0,X1)) & (sP5(X2,X0,X1) | ~r2_lattice3(X0,X1,X2))) | ~sP6(X1,X0,X2))),
% 11.33/1.78    inference(nnf_transformation,[],[f40])).
% 11.33/1.78  fof(f807,plain,(
% 11.33/1.78    r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11)) | ~spl15_76),
% 11.33/1.78    inference(avatar_component_clause,[],[f806])).
% 11.33/1.78  fof(f806,plain,(
% 11.33/1.78    spl15_76 <=> r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).
% 11.33/1.78  fof(f8589,plain,(
% 11.33/1.78    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) | ~spl15_814),
% 11.33/1.78    inference(avatar_component_clause,[],[f8588])).
% 11.33/1.78  fof(f8588,plain,(
% 11.33/1.78    spl15_814 <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11)),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_814])])).
% 11.33/1.78  fof(f33688,plain,(
% 11.33/1.78    spl15_3232 | spl15_814 | ~spl15_5 | ~spl15_71 | ~spl15_153 | ~spl15_561 | ~spl15_572),
% 11.33/1.78    inference(avatar_split_clause,[],[f33687,f6140,f6084,f1605,f781,f148,f8588,f33596])).
% 11.33/1.78  fof(f33596,plain,(
% 11.33/1.78    spl15_3232 <=> k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_3232])])).
% 11.33/1.78  fof(f781,plain,(
% 11.33/1.78    spl15_71 <=> m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_71])])).
% 11.33/1.78  fof(f1605,plain,(
% 11.33/1.78    spl15_153 <=> m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_153])])).
% 11.33/1.78  fof(f6084,plain,(
% 11.33/1.78    spl15_561 <=> sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9)),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_561])])).
% 11.33/1.78  fof(f6140,plain,(
% 11.33/1.78    spl15_572 <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10))),
% 11.33/1.78    introduced(avatar_definition,[new_symbols(naming,[spl15_572])])).
% 11.33/1.78  fof(f33687,plain,(
% 11.33/1.78    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | (~spl15_5 | ~spl15_71 | ~spl15_153 | ~spl15_561 | ~spl15_572)),
% 11.33/1.78    inference(subsumption_resolution,[],[f33686,f6086])).
% 11.33/1.78  fof(f6086,plain,(
% 11.33/1.78    sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) | ~spl15_561),
% 11.33/1.78    inference(avatar_component_clause,[],[f6084])).
% 11.33/1.78  fof(f33686,plain,(
% 11.33/1.78    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) | (~spl15_5 | ~spl15_71 | ~spl15_153 | ~spl15_572)),
% 11.33/1.78    inference(subsumption_resolution,[],[f33685,f6142])).
% 11.33/1.78  fof(f6142,plain,(
% 11.33/1.78    r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~spl15_572),
% 11.33/1.78    inference(avatar_component_clause,[],[f6140])).
% 11.33/1.78  fof(f33685,plain,(
% 11.33/1.78    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) | (~spl15_5 | ~spl15_71 | ~spl15_153)),
% 11.33/1.78    inference(subsumption_resolution,[],[f33586,f783])).
% 11.33/1.78  fof(f783,plain,(
% 11.33/1.78    m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9)) | ~spl15_71),
% 11.33/1.78    inference(avatar_component_clause,[],[f781])).
% 11.33/1.78  fof(f33586,plain,(
% 11.33/1.78    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK11) | k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9)) | ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) | (~spl15_5 | ~spl15_153)),
% 11.33/1.78    inference(resolution,[],[f1607,f8816])).
% 11.33/1.78  fof(f8816,plain,(
% 11.33/1.78    ( ! [X0] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10)) | r2_hidden(X0,sK11) | k1_xboole_0 = k1_tarski(X0) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r1_orders_2(sK9,X0,X0) | ~sP1(X0,X0,sK9)) ) | ~spl15_5),
% 11.33/1.78    inference(resolution,[],[f4613,f96])).
% 11.33/1.78  fof(f96,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (r2_lattice3(X2,k1_tarski(X1),X0) | ~r1_orders_2(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f54])).
% 11.33/1.78  fof(f54,plain,(
% 11.33/1.78    ! [X0,X1,X2] : (((r2_lattice3(X2,k1_tarski(X1),X0) | ~r1_orders_2(X2,X1,X0)) & (r1_orders_2(X2,X1,X0) | ~r2_lattice3(X2,k1_tarski(X1),X0)) & (r1_lattice3(X2,k1_tarski(X1),X0) | ~r1_orders_2(X2,X0,X1)) & (r1_orders_2(X2,X0,X1) | ~r1_lattice3(X2,k1_tarski(X1),X0))) | ~sP1(X0,X1,X2))),
% 11.33/1.78    inference(rectify,[],[f53])).
% 11.33/1.78  fof(f53,plain,(
% 11.33/1.78    ! [X1,X2,X0] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~sP1(X1,X2,X0))),
% 11.33/1.78    inference(nnf_transformation,[],[f33])).
% 11.33/1.78  fof(f33,plain,(
% 11.33/1.78    ! [X1,X2,X0] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~sP1(X1,X2,X0))),
% 11.33/1.78    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.33/1.78  fof(f4613,plain,(
% 11.33/1.78    ( ! [X0] : (~r2_lattice3(sK9,k1_tarski(X0),X0) | k1_xboole_0 = k1_tarski(X0) | r2_hidden(X0,sK11) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10)) | ~m1_subset_1(X0,u1_struct_0(sK9))) ) | ~spl15_5),
% 11.33/1.78    inference(subsumption_resolution,[],[f4612,f92])).
% 11.33/1.78  fof(f92,plain,(
% 11.33/1.78    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 11.33/1.78    inference(cnf_transformation,[],[f6])).
% 11.33/1.78  fof(f6,axiom,(
% 11.33/1.78    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 11.33/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 11.33/1.78  fof(f4612,plain,(
% 11.33/1.78    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK9)) | ~v1_finset_1(k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | r2_hidden(X0,sK11) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10)) | ~r2_lattice3(sK9,k1_tarski(X0),X0)) ) | ~spl15_5),
% 11.33/1.78    inference(subsumption_resolution,[],[f4591,f150])).
% 11.33/1.78  fof(f4591,plain,(
% 11.33/1.78    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK9)) | ~l1_orders_2(sK9) | ~v1_finset_1(k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | r2_hidden(X0,sK11) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10)) | ~r2_lattice3(sK9,k1_tarski(X0),X0)) ) | ~spl15_5),
% 11.33/1.78    inference(duplicate_literal_removal,[],[f4588])).
% 11.33/1.78  fof(f4588,plain,(
% 11.33/1.78    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK9)) | ~l1_orders_2(sK9) | ~v1_finset_1(k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | r2_hidden(X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK10)) | ~r2_lattice3(sK9,k1_tarski(X0),X0)) ) | ~spl15_5),
% 11.33/1.78    inference(resolution,[],[f2234,f1748])).
% 11.33/1.78  fof(f1748,plain,(
% 11.33/1.78    ( ! [X0,X1] : (~sP2(X1,sK9,X0) | ~v1_finset_1(X0) | k1_xboole_0 = X0 | r2_hidden(X1,sK11) | ~m1_subset_1(X1,u1_struct_0(sK9)) | ~m1_subset_1(X0,k1_zfmisc_1(sK10)) | ~r2_lattice3(sK9,X0,X1)) ) | ~spl15_5),
% 11.33/1.78    inference(resolution,[],[f906,f104])).
% 11.33/1.78  fof(f104,plain,(
% 11.33/1.78    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r2_lattice3(X1,X0,X2)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f59])).
% 11.33/1.78  fof(f59,plain,(
% 11.33/1.78    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r2_lattice3(X1,X0,X2)) & ((sP2(X2,X1,X0) & r2_lattice3(X1,X0,X2)) | ~sP3(X0,X1,X2)))),
% 11.33/1.78    inference(rectify,[],[f58])).
% 11.33/1.78  fof(f58,plain,(
% 11.33/1.78    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2)) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 11.33/1.78    inference(flattening,[],[f57])).
% 11.33/1.78  fof(f57,plain,(
% 11.33/1.78    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2))) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 11.33/1.78    inference(nnf_transformation,[],[f36])).
% 11.33/1.78  fof(f36,plain,(
% 11.33/1.78    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)))),
% 11.33/1.78    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 11.33/1.78  fof(f906,plain,(
% 11.33/1.78    ( ! [X0,X1] : (~sP3(X0,sK9,X1) | ~m1_subset_1(X0,k1_zfmisc_1(sK10)) | ~v1_finset_1(X0) | k1_xboole_0 = X0 | r2_hidden(X1,sK11) | ~m1_subset_1(X1,u1_struct_0(sK9))) ) | ~spl15_5),
% 11.33/1.78    inference(subsumption_resolution,[],[f905,f85])).
% 11.33/1.78  fof(f85,plain,(
% 11.33/1.78    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(sK10)) | k1_xboole_0 = X5 | r1_yellow_0(sK9,X5) | ~v1_finset_1(X5)) )),
% 11.33/1.78    inference(cnf_transformation,[],[f52])).
% 11.33/1.78  fof(f52,plain,(
% 11.33/1.78    ((k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11) & r1_yellow_0(sK9,sK10) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),sK11) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK10)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,sK10) | ~r2_hidden(X4,sK11) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(sK10)) | ~v1_finset_1(X5)) & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))) & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))) & l1_orders_2(sK9) & v4_orders_2(sK9) & v3_orders_2(sK9) & ~v2_struct_0(sK9)),
% 11.33/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f48,f51,f50,f49])).
% 11.33/1.78  fof(f49,plain,(
% 11.33/1.78    ? [X0] : (? [X1] : (? [X2] : (k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,X0,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X5] : (r1_yellow_0(X0,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X1)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_yellow_0(sK9,X1) != k1_yellow_0(sK9,X2) & r1_yellow_0(sK9,X1) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X1)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))) & l1_orders_2(sK9) & v4_orders_2(sK9) & v3_orders_2(sK9) & ~v2_struct_0(sK9))),
% 11.33/1.78    introduced(choice_axiom,[])).
% 11.33/1.78  fof(f50,plain,(
% 11.33/1.78    ? [X1] : (? [X2] : (k1_yellow_0(sK9,X1) != k1_yellow_0(sK9,X2) & r1_yellow_0(sK9,X1) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X1)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))) => (? [X2] : (k1_yellow_0(sK9,X2) != k1_yellow_0(sK9,sK10) & r1_yellow_0(sK9,sK10) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK10)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,sK10) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(sK10)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))) & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))))),
% 11.33/1.78    introduced(choice_axiom,[])).
% 11.33/1.78  fof(f51,plain,(
% 11.33/1.78    ? [X2] : (k1_yellow_0(sK9,X2) != k1_yellow_0(sK9,sK10) & r1_yellow_0(sK9,sK10) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK10)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,sK10) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(sK10)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))) => (k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11) & r1_yellow_0(sK9,sK10) & ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),sK11) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK10)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,sK9,sK10) | ~r2_hidden(X4,sK11) | ~m1_subset_1(X4,u1_struct_0(sK9))) & ! [X5] : (r1_yellow_0(sK9,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(sK10)) | ~v1_finset_1(X5)) & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))))),
% 11.33/1.78    introduced(choice_axiom,[])).
% 11.33/1.78  fof(f48,plain,(
% 11.33/1.78    ? [X0] : (? [X1] : (? [X2] : (k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,X0,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X5] : (r1_yellow_0(X0,X5) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X1)) | ~v1_finset_1(X5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.33/1.78    inference(rectify,[],[f32])).
% 11.33/1.78  fof(f32,plain,(
% 11.33/1.78    ? [X0] : (? [X1] : (? [X2] : (k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (sP0(X4,X0,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.33/1.78    inference(definition_folding,[],[f17,f31])).
% 11.33/1.78  fof(f31,plain,(
% 11.33/1.78    ! [X4,X0,X1] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~sP0(X4,X0,X1))),
% 11.33/1.78    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.33/1.78  fof(f17,plain,(
% 11.33/1.78    ? [X0] : (? [X1] : (? [X2] : (k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.33/1.78    inference(flattening,[],[f16])).
% 11.33/1.78  fof(f16,plain,(
% 11.33/1.78    ? [X0] : (? [X1] : (? [X2] : ((k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2) & (r1_yellow_0(X0,X1) & ! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.33/1.78    inference(ennf_transformation,[],[f15])).
% 11.33/1.78  fof(f15,plain,(
% 11.33/1.78    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_yellow_0(X0,X1) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))))),
% 11.33/1.78    inference(rectify,[],[f14])).
% 11.33/1.78  fof(f14,negated_conjecture,(
% 11.33/1.78    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_yellow_0(X0,X1) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))))),
% 11.33/1.78    inference(negated_conjecture,[],[f13])).
% 11.33/1.78  fof(f13,conjecture,(
% 11.33/1.78    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_yellow_0(X0,X1) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))))),
% 11.33/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_waybel_0)).
% 11.33/1.79  fof(f905,plain,(
% 11.33/1.79    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK10)) | ~v1_finset_1(X0) | ~sP3(X0,sK9,X1) | r2_hidden(X1,sK11) | ~r1_yellow_0(sK9,X0) | ~m1_subset_1(X1,u1_struct_0(sK9))) ) | ~spl15_5),
% 11.33/1.79    inference(subsumption_resolution,[],[f903,f150])).
% 11.33/1.79  fof(f903,plain,(
% 11.33/1.79    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK10)) | ~v1_finset_1(X0) | ~sP3(X0,sK9,X1) | r2_hidden(X1,sK11) | ~r1_yellow_0(sK9,X0) | ~m1_subset_1(X1,u1_struct_0(sK9)) | ~l1_orders_2(sK9)) )),
% 11.33/1.79    inference(resolution,[],[f275,f109])).
% 11.33/1.79  fof(f109,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f38])).
% 11.33/1.79  fof(f38,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(definition_folding,[],[f21,f37,f36,f35])).
% 11.33/1.79  fof(f35,plain,(
% 11.33/1.79    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 11.33/1.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 11.33/1.79  fof(f37,plain,(
% 11.33/1.79    ! [X2,X0,X1] : ((k1_yellow_0(X0,X1) = X2 <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 11.33/1.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 11.33/1.79  fof(f21,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(flattening,[],[f20])).
% 11.33/1.79  fof(f20,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(ennf_transformation,[],[f9])).
% 11.33/1.79  fof(f9,axiom,(
% 11.33/1.79    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 11.33/1.79  fof(f275,plain,(
% 11.33/1.79    ( ! [X2,X1] : (~sP4(X2,sK9,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(sK10)) | ~v1_finset_1(X1) | ~sP3(X1,sK9,X2) | r2_hidden(X2,sK11)) )),
% 11.33/1.79    inference(superposition,[],[f87,f101])).
% 11.33/1.79  fof(f101,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (k1_yellow_0(X1,X2) = X0 | ~sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f56])).
% 11.33/1.79  fof(f56,plain,(
% 11.33/1.79    ! [X0,X1,X2] : (((k1_yellow_0(X1,X2) = X0 | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0)) | ~sP4(X0,X1,X2))),
% 11.33/1.79    inference(rectify,[],[f55])).
% 11.33/1.79  fof(f55,plain,(
% 11.33/1.79    ! [X2,X0,X1] : (((k1_yellow_0(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k1_yellow_0(X0,X1) != X2)) | ~sP4(X2,X0,X1))),
% 11.33/1.79    inference(nnf_transformation,[],[f37])).
% 11.33/1.79  fof(f87,plain,(
% 11.33/1.79    ( ! [X3] : (r2_hidden(k1_yellow_0(sK9,X3),sK11) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK10)) | ~v1_finset_1(X3)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f2234,plain,(
% 11.33/1.79    ( ! [X0,X1] : (sP2(X0,X1,k1_tarski(X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 11.33/1.79    inference(duplicate_literal_removal,[],[f2233])).
% 11.33/1.79  fof(f2233,plain,(
% 11.33/1.79    ( ! [X0,X1] : (sP2(X0,X1,k1_tarski(X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | sP2(X0,X1,k1_tarski(X0))) )),
% 11.33/1.79    inference(resolution,[],[f1381,f108])).
% 11.33/1.79  fof(f108,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,sK12(X0,X1,X2)) | sP2(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f63])).
% 11.33/1.79  fof(f63,plain,(
% 11.33/1.79    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_orders_2(X1,X0,sK12(X0,X1,X2)) & r2_lattice3(X1,X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 11.33/1.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f61,f62])).
% 11.33/1.79  fof(f62,plain,(
% 11.33/1.79    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK12(X0,X1,X2)) & r2_lattice3(X1,X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 11.33/1.79    introduced(choice_axiom,[])).
% 11.33/1.79  fof(f61,plain,(
% 11.33/1.79    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 11.33/1.79    inference(rectify,[],[f60])).
% 11.33/1.79  fof(f60,plain,(
% 11.33/1.79    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X0,X1)))),
% 11.33/1.79    inference(nnf_transformation,[],[f35])).
% 11.33/1.79  fof(f1381,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1))) | sP2(X2,X0,k1_tarski(X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.79    inference(subsumption_resolution,[],[f1380,f106])).
% 11.33/1.79  fof(f106,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f63])).
% 11.33/1.79  fof(f1380,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1))) | sP2(X2,X0,k1_tarski(X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK12(X2,X0,k1_tarski(X1)),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.79    inference(resolution,[],[f268,f97])).
% 11.33/1.79  fof(f97,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f34])).
% 11.33/1.79  fof(f34,plain,(
% 11.33/1.79    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(definition_folding,[],[f18,f33])).
% 11.33/1.79  fof(f18,plain,(
% 11.33/1.79    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(ennf_transformation,[],[f11])).
% 11.33/1.79  fof(f11,axiom,(
% 11.33/1.79    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 11.33/1.79  fof(f268,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~sP1(sK12(X2,X0,k1_tarski(X1)),X1,X0) | r1_orders_2(X0,X1,sK12(X2,X0,k1_tarski(X1))) | sP2(X2,X0,k1_tarski(X1))) )),
% 11.33/1.79    inference(resolution,[],[f95,f107])).
% 11.33/1.79  fof(f107,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (r2_lattice3(X1,X2,sK12(X0,X1,X2)) | sP2(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f63])).
% 11.33/1.79  fof(f95,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~r2_lattice3(X2,k1_tarski(X1),X0) | r1_orders_2(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f54])).
% 11.33/1.79  fof(f1607,plain,(
% 11.33/1.79    m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10)) | ~spl15_153),
% 11.33/1.79    inference(avatar_component_clause,[],[f1605])).
% 11.33/1.79  fof(f33684,plain,(
% 11.33/1.79    ~spl15_9 | ~spl15_3232),
% 11.33/1.79    inference(avatar_contradiction_clause,[],[f33683])).
% 11.33/1.79  fof(f33683,plain,(
% 11.33/1.79    $false | (~spl15_9 | ~spl15_3232)),
% 11.33/1.79    inference(subsumption_resolution,[],[f33631,f170])).
% 11.33/1.79  fof(f170,plain,(
% 11.33/1.79    v1_xboole_0(k1_xboole_0) | ~spl15_9),
% 11.33/1.79    inference(avatar_component_clause,[],[f168])).
% 11.33/1.79  fof(f168,plain,(
% 11.33/1.79    spl15_9 <=> v1_xboole_0(k1_xboole_0)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).
% 11.33/1.79  fof(f33631,plain,(
% 11.33/1.79    ~v1_xboole_0(k1_xboole_0) | ~spl15_3232),
% 11.33/1.79    inference(superposition,[],[f91,f33598])).
% 11.33/1.79  fof(f33598,plain,(
% 11.33/1.79    k1_xboole_0 = k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | ~spl15_3232),
% 11.33/1.79    inference(avatar_component_clause,[],[f33596])).
% 11.33/1.79  fof(f91,plain,(
% 11.33/1.79    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 11.33/1.79    inference(cnf_transformation,[],[f2])).
% 11.33/1.79  fof(f2,axiom,(
% 11.33/1.79    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 11.33/1.79  fof(f22512,plain,(
% 11.33/1.79    ~spl15_1190 | ~spl15_5 | ~spl15_51 | ~spl15_88 | spl15_89 | ~spl15_168),
% 11.33/1.79    inference(avatar_split_clause,[],[f21840,f1744,f922,f917,f628,f148,f12354])).
% 11.33/1.79  fof(f12354,plain,(
% 11.33/1.79    spl15_1190 <=> r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11))),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_1190])])).
% 11.33/1.79  fof(f917,plain,(
% 11.33/1.79    spl15_88 <=> m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9))),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_88])])).
% 11.33/1.79  fof(f922,plain,(
% 11.33/1.79    spl15_89 <=> r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11))),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_89])])).
% 11.33/1.79  fof(f1744,plain,(
% 11.33/1.79    spl15_168 <=> sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_168])])).
% 11.33/1.79  fof(f21840,plain,(
% 11.33/1.79    ~r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) | (~spl15_5 | ~spl15_51 | ~spl15_88 | spl15_89 | ~spl15_168)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f150,f630,f1746,f919,f924,f4772])).
% 11.33/1.79  fof(f4772,plain,(
% 11.33/1.79    ( ! [X4,X2,X5,X3] : (~r2_lattice3(X2,sK8(X3,X2,X4),X5) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~sP0(X3,X2,X4) | ~l1_orders_2(X2) | ~m1_subset_1(X5,u1_struct_0(X2)) | r1_orders_2(X2,X3,X5)) )),
% 11.33/1.79    inference(resolution,[],[f2004,f105])).
% 11.33/1.79  fof(f105,plain,(
% 11.33/1.79    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f63])).
% 11.33/1.79  fof(f2004,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP2(X1,X0,sK8(X1,X0,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~sP0(X1,X0,X2)) )),
% 11.33/1.79    inference(subsumption_resolution,[],[f2001,f77])).
% 11.33/1.79  fof(f77,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (r1_yellow_0(X1,sK8(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f47])).
% 11.33/1.79  fof(f47,plain,(
% 11.33/1.79    ! [X0,X1,X2] : ((k1_yellow_0(X1,sK8(X0,X1,X2)) = X0 & r1_yellow_0(X1,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2)) & v1_finset_1(sK8(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 11.33/1.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f46])).
% 11.33/1.79  fof(f46,plain,(
% 11.33/1.79    ! [X2,X1,X0] : (? [X3] : (k1_yellow_0(X1,X3) = X0 & r1_yellow_0(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(X2)) & v1_finset_1(X3)) => (k1_yellow_0(X1,sK8(X0,X1,X2)) = X0 & r1_yellow_0(X1,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2)) & v1_finset_1(sK8(X0,X1,X2))))),
% 11.33/1.79    introduced(choice_axiom,[])).
% 11.33/1.79  fof(f45,plain,(
% 11.33/1.79    ! [X0,X1,X2] : (? [X3] : (k1_yellow_0(X1,X3) = X0 & r1_yellow_0(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(X2)) & v1_finset_1(X3)) | ~sP0(X0,X1,X2))),
% 11.33/1.79    inference(rectify,[],[f44])).
% 11.33/1.79  fof(f44,plain,(
% 11.33/1.79    ! [X4,X0,X1] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~sP0(X4,X0,X1))),
% 11.33/1.79    inference(nnf_transformation,[],[f31])).
% 11.33/1.79  fof(f2001,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP2(X1,X0,sK8(X1,X0,X2)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,sK8(X1,X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~sP0(X1,X0,X2)) )),
% 11.33/1.79    inference(superposition,[],[f1149,f78])).
% 11.33/1.79  fof(f78,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (k1_yellow_0(X1,sK8(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f47])).
% 11.33/1.79  fof(f1149,plain,(
% 11.33/1.79    ( ! [X0,X1] : (sP2(k1_yellow_0(X0,X1),X0,X1) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 11.33/1.79    inference(resolution,[],[f303,f103])).
% 11.33/1.79  fof(f103,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | sP2(X2,X1,X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f59])).
% 11.33/1.79  fof(f303,plain,(
% 11.33/1.79    ( ! [X0,X1] : (sP3(X1,X0,k1_yellow_0(X0,X1)) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1)) )),
% 11.33/1.79    inference(resolution,[],[f109,f126])).
% 11.33/1.79  fof(f126,plain,(
% 11.33/1.79    ( ! [X2,X1] : (~sP4(k1_yellow_0(X1,X2),X1,X2) | sP3(X2,X1,k1_yellow_0(X1,X2))) )),
% 11.33/1.79    inference(equality_resolution,[],[f100])).
% 11.33/1.79  fof(f100,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0 | ~sP4(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f56])).
% 11.33/1.79  fof(f924,plain,(
% 11.33/1.79    ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11)) | spl15_89),
% 11.33/1.79    inference(avatar_component_clause,[],[f922])).
% 11.33/1.79  fof(f919,plain,(
% 11.33/1.79    m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9)) | ~spl15_88),
% 11.33/1.79    inference(avatar_component_clause,[],[f917])).
% 11.33/1.79  fof(f1746,plain,(
% 11.33/1.79    sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10) | ~spl15_168),
% 11.33/1.79    inference(avatar_component_clause,[],[f1744])).
% 11.33/1.79  fof(f22404,plain,(
% 11.33/1.79    ~spl15_76 | ~spl15_62 | ~spl15_61),
% 11.33/1.79    inference(avatar_split_clause,[],[f3466,f708,f714,f806])).
% 11.33/1.79  fof(f714,plain,(
% 11.33/1.79    spl15_62 <=> r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11))),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).
% 11.33/1.79  fof(f708,plain,(
% 11.33/1.79    spl15_61 <=> sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_61])])).
% 11.33/1.79  fof(f3466,plain,(
% 11.33/1.79    ~r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11)) | ~r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11)) | ~spl15_61),
% 11.33/1.79    inference(resolution,[],[f710,f119])).
% 11.33/1.79  fof(f119,plain,(
% 11.33/1.79    ( ! [X2,X0,X3,X1] : (~sP7(X0,X1,X2,X3) | ~r2_lattice3(X2,X3,X0) | ~r2_lattice3(X2,X1,X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f71])).
% 11.33/1.79  fof(f71,plain,(
% 11.33/1.79    ! [X0,X1,X2,X3] : (((~r2_lattice3(X2,X1,X0) | ~r2_lattice3(X2,X3,X0)) & (r2_lattice3(X2,X1,X0) | r2_lattice3(X2,X3,X0))) | ~sP7(X0,X1,X2,X3))),
% 11.33/1.79    inference(rectify,[],[f70])).
% 11.33/1.79  fof(f70,plain,(
% 11.33/1.79    ! [X3,X2,X0,X1] : (((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3))) | ~sP7(X3,X2,X0,X1))),
% 11.33/1.79    inference(nnf_transformation,[],[f42])).
% 11.33/1.79  fof(f42,plain,(
% 11.33/1.79    ! [X3,X2,X0,X1] : ((r2_lattice3(X0,X1,X3) <~> r2_lattice3(X0,X2,X3)) | ~sP7(X3,X2,X0,X1))),
% 11.33/1.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 11.33/1.79  fof(f710,plain,(
% 11.33/1.79    sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10) | ~spl15_61),
% 11.33/1.79    inference(avatar_component_clause,[],[f708])).
% 11.33/1.79  fof(f22380,plain,(
% 11.33/1.79    spl15_76 | spl15_62 | ~spl15_61),
% 11.33/1.79    inference(avatar_split_clause,[],[f3467,f708,f714,f806])).
% 11.33/1.79  fof(f3467,plain,(
% 11.33/1.79    r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11)) | r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11)) | ~spl15_61),
% 11.33/1.79    inference(resolution,[],[f710,f118])).
% 11.33/1.79  fof(f118,plain,(
% 11.33/1.79    ( ! [X2,X0,X3,X1] : (~sP7(X0,X1,X2,X3) | r2_lattice3(X2,X3,X0) | r2_lattice3(X2,X1,X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f71])).
% 11.33/1.79  fof(f12357,plain,(
% 11.33/1.79    spl15_1190 | ~spl15_5 | ~spl15_51 | ~spl15_62 | ~spl15_531),
% 11.33/1.79    inference(avatar_split_clause,[],[f12322,f5832,f714,f628,f148,f12354])).
% 11.33/1.79  fof(f5832,plain,(
% 11.33/1.79    spl15_531 <=> r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_531])])).
% 11.33/1.79  fof(f12322,plain,(
% 11.33/1.79    r2_lattice3(sK9,sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) | (~spl15_5 | ~spl15_51 | ~spl15_62 | ~spl15_531)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f150,f715,f630,f5834,f99])).
% 11.33/1.79  fof(f99,plain,(
% 11.33/1.79    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f19])).
% 11.33/1.79  fof(f19,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 11.33/1.79    inference(ennf_transformation,[],[f12])).
% 11.33/1.79  fof(f12,axiom,(
% 11.33/1.79    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 11.33/1.79  fof(f5834,plain,(
% 11.33/1.79    r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10) | ~spl15_531),
% 11.33/1.79    inference(avatar_component_clause,[],[f5832])).
% 11.33/1.79  fof(f715,plain,(
% 11.33/1.79    r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11)) | ~spl15_62),
% 11.33/1.79    inference(avatar_component_clause,[],[f714])).
% 11.33/1.79  fof(f6143,plain,(
% 11.33/1.79    spl15_572 | ~spl15_5 | ~spl15_7 | spl15_8 | ~spl15_71),
% 11.33/1.79    inference(avatar_split_clause,[],[f6016,f781,f163,f158,f148,f6140])).
% 11.33/1.79  fof(f158,plain,(
% 11.33/1.79    spl15_7 <=> v3_orders_2(sK9)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).
% 11.33/1.79  fof(f163,plain,(
% 11.33/1.79    spl15_8 <=> v2_struct_0(sK9)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).
% 11.33/1.79  fof(f6016,plain,(
% 11.33/1.79    r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10)) | (~spl15_5 | ~spl15_7 | spl15_8 | ~spl15_71)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f165,f160,f150,f783,f117])).
% 11.33/1.79  fof(f117,plain,(
% 11.33/1.79    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f25])).
% 11.33/1.79  fof(f25,plain,(
% 11.33/1.79    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.33/1.79    inference(flattening,[],[f24])).
% 11.33/1.79  fof(f24,plain,(
% 11.33/1.79    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.33/1.79    inference(ennf_transformation,[],[f7])).
% 11.33/1.79  fof(f7,axiom,(
% 11.33/1.79    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 11.33/1.79  fof(f160,plain,(
% 11.33/1.79    v3_orders_2(sK9) | ~spl15_7),
% 11.33/1.79    inference(avatar_component_clause,[],[f158])).
% 11.33/1.79  fof(f165,plain,(
% 11.33/1.79    ~v2_struct_0(sK9) | spl15_8),
% 11.33/1.79    inference(avatar_component_clause,[],[f163])).
% 11.33/1.79  fof(f6118,plain,(
% 11.33/1.79    spl15_561 | ~spl15_5 | ~spl15_71),
% 11.33/1.79    inference(avatar_split_clause,[],[f6006,f781,f148,f6084])).
% 11.33/1.79  fof(f6006,plain,(
% 11.33/1.79    sP1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK9) | (~spl15_5 | ~spl15_71)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f150,f783,f783,f97])).
% 11.33/1.79  fof(f5835,plain,(
% 11.33/1.79    spl15_531 | ~spl15_168),
% 11.33/1.79    inference(avatar_split_clause,[],[f5808,f1744,f5832])).
% 11.33/1.79  fof(f5808,plain,(
% 11.33/1.79    r1_tarski(sK8(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10),sK10) | ~spl15_168),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f1746,f205])).
% 11.33/1.79  fof(f205,plain,(
% 11.33/1.79    ( ! [X6,X8,X7] : (r1_tarski(sK8(X6,X7,X8),X8) | ~sP0(X6,X7,X8)) )),
% 11.33/1.79    inference(resolution,[],[f76,f123])).
% 11.33/1.79  fof(f123,plain,(
% 11.33/1.79    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f74])).
% 11.33/1.79  fof(f74,plain,(
% 11.33/1.79    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.33/1.79    inference(nnf_transformation,[],[f4])).
% 11.33/1.79  fof(f4,axiom,(
% 11.33/1.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 11.33/1.79  fof(f76,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2)) | ~sP0(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f47])).
% 11.33/1.79  fof(f1747,plain,(
% 11.33/1.79    spl15_168 | ~spl15_87 | ~spl15_88),
% 11.33/1.79    inference(avatar_split_clause,[],[f1708,f917,f912,f1744])).
% 11.33/1.79  fof(f912,plain,(
% 11.33/1.79    spl15_87 <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_87])])).
% 11.33/1.79  fof(f1708,plain,(
% 11.33/1.79    sP0(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK9,sK10) | (~spl15_87 | ~spl15_88)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f914,f919,f86])).
% 11.33/1.79  fof(f86,plain,(
% 11.33/1.79    ( ! [X4] : (sP0(X4,sK9,sK10) | ~r2_hidden(X4,sK11) | ~m1_subset_1(X4,u1_struct_0(sK9))) )),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f914,plain,(
% 11.33/1.79    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11) | ~spl15_87),
% 11.33/1.79    inference(avatar_component_clause,[],[f912])).
% 11.33/1.79  fof(f1608,plain,(
% 11.33/1.79    spl15_153 | ~spl15_70),
% 11.33/1.79    inference(avatar_split_clause,[],[f1603,f776,f1605])).
% 11.33/1.79  fof(f776,plain,(
% 11.33/1.79    spl15_70 <=> r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).
% 11.33/1.79  fof(f1603,plain,(
% 11.33/1.79    m1_subset_1(k1_tarski(sK13(sK14(sK9,sK10,sK11),sK9,sK10)),k1_zfmisc_1(sK10)) | ~spl15_70),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f778,f122])).
% 11.33/1.79  fof(f122,plain,(
% 11.33/1.79    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f28])).
% 11.33/1.79  fof(f28,plain,(
% 11.33/1.79    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.33/1.79    inference(ennf_transformation,[],[f3])).
% 11.33/1.79  fof(f3,axiom,(
% 11.33/1.79    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 11.33/1.79  fof(f778,plain,(
% 11.33/1.79    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10) | ~spl15_70),
% 11.33/1.79    inference(avatar_component_clause,[],[f776])).
% 11.33/1.79  fof(f925,plain,(
% 11.33/1.79    ~spl15_89 | spl15_85),
% 11.33/1.79    inference(avatar_split_clause,[],[f908,f890,f922])).
% 11.33/1.79  fof(f890,plain,(
% 11.33/1.79    spl15_85 <=> sP5(sK14(sK9,sK10,sK11),sK9,sK11)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_85])])).
% 11.33/1.79  fof(f908,plain,(
% 11.33/1.79    ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK14(sK9,sK10,sK11)) | spl15_85),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f892,f115])).
% 11.33/1.79  fof(f115,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~r1_orders_2(X1,sK13(X0,X1,X2),X0) | sP5(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f69])).
% 11.33/1.79  fof(f892,plain,(
% 11.33/1.79    ~sP5(sK14(sK9,sK10,sK11),sK9,sK11) | spl15_85),
% 11.33/1.79    inference(avatar_component_clause,[],[f890])).
% 11.33/1.79  fof(f920,plain,(
% 11.33/1.79    spl15_88 | spl15_85),
% 11.33/1.79    inference(avatar_split_clause,[],[f909,f890,f917])).
% 11.33/1.79  fof(f909,plain,(
% 11.33/1.79    m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK11),u1_struct_0(sK9)) | spl15_85),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f892,f113])).
% 11.33/1.79  fof(f113,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) | sP5(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f69])).
% 11.33/1.79  fof(f915,plain,(
% 11.33/1.79    spl15_87 | spl15_85),
% 11.33/1.79    inference(avatar_split_clause,[],[f910,f890,f912])).
% 11.33/1.79  fof(f910,plain,(
% 11.33/1.79    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK11),sK11) | spl15_85),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f892,f114])).
% 11.33/1.79  fof(f114,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (r2_hidden(sK13(X0,X1,X2),X2) | sP5(X0,X1,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f69])).
% 11.33/1.79  fof(f893,plain,(
% 11.33/1.79    ~spl15_85 | ~spl15_5 | ~spl15_51 | spl15_76),
% 11.33/1.79    inference(avatar_split_clause,[],[f886,f806,f628,f148,f890])).
% 11.33/1.79  fof(f886,plain,(
% 11.33/1.79    ~sP5(sK14(sK9,sK10,sK11),sK9,sK11) | (~spl15_5 | ~spl15_51 | spl15_76)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f637,f808,f111])).
% 11.33/1.79  fof(f111,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (~sP6(X0,X1,X2) | ~sP5(X2,X1,X0) | r2_lattice3(X1,X0,X2)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f65])).
% 11.33/1.79  fof(f808,plain,(
% 11.33/1.79    ~r2_lattice3(sK9,sK11,sK14(sK9,sK10,sK11)) | spl15_76),
% 11.33/1.79    inference(avatar_component_clause,[],[f806])).
% 11.33/1.79  fof(f637,plain,(
% 11.33/1.79    ( ! [X0] : (sP6(X0,sK9,sK14(sK9,sK10,sK11))) ) | (~spl15_5 | ~spl15_51)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f150,f630,f116])).
% 11.33/1.79  fof(f789,plain,(
% 11.33/1.79    ~spl15_72 | spl15_64),
% 11.33/1.79    inference(avatar_split_clause,[],[f772,f729,f786])).
% 11.33/1.79  fof(f729,plain,(
% 11.33/1.79    spl15_64 <=> sP5(sK14(sK9,sK10,sK11),sK9,sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).
% 11.33/1.79  fof(f772,plain,(
% 11.33/1.79    ~r1_orders_2(sK9,sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK14(sK9,sK10,sK11)) | spl15_64),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f731,f115])).
% 11.33/1.79  fof(f731,plain,(
% 11.33/1.79    ~sP5(sK14(sK9,sK10,sK11),sK9,sK10) | spl15_64),
% 11.33/1.79    inference(avatar_component_clause,[],[f729])).
% 11.33/1.79  fof(f784,plain,(
% 11.33/1.79    spl15_71 | spl15_64),
% 11.33/1.79    inference(avatar_split_clause,[],[f773,f729,f781])).
% 11.33/1.79  fof(f773,plain,(
% 11.33/1.79    m1_subset_1(sK13(sK14(sK9,sK10,sK11),sK9,sK10),u1_struct_0(sK9)) | spl15_64),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f731,f113])).
% 11.33/1.79  fof(f779,plain,(
% 11.33/1.79    spl15_70 | spl15_64),
% 11.33/1.79    inference(avatar_split_clause,[],[f774,f729,f776])).
% 11.33/1.79  fof(f774,plain,(
% 11.33/1.79    r2_hidden(sK13(sK14(sK9,sK10,sK11),sK9,sK10),sK10) | spl15_64),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f731,f114])).
% 11.33/1.79  fof(f732,plain,(
% 11.33/1.79    ~spl15_64 | ~spl15_5 | ~spl15_51 | spl15_62),
% 11.33/1.79    inference(avatar_split_clause,[],[f725,f714,f628,f148,f729])).
% 11.33/1.79  fof(f725,plain,(
% 11.33/1.79    ~sP5(sK14(sK9,sK10,sK11),sK9,sK10) | (~spl15_5 | ~spl15_51 | spl15_62)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f637,f716,f111])).
% 11.33/1.79  fof(f716,plain,(
% 11.33/1.79    ~r2_lattice3(sK9,sK10,sK14(sK9,sK10,sK11)) | spl15_62),
% 11.33/1.79    inference(avatar_component_clause,[],[f714])).
% 11.33/1.79  fof(f711,plain,(
% 11.33/1.79    spl15_61 | spl15_1 | ~spl15_2 | ~spl15_5 | spl15_8),
% 11.33/1.79    inference(avatar_split_clause,[],[f703,f163,f148,f133,f128,f708])).
% 11.33/1.79  fof(f128,plain,(
% 11.33/1.79    spl15_1 <=> k1_yellow_0(sK9,sK10) = k1_yellow_0(sK9,sK11)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 11.33/1.79  fof(f133,plain,(
% 11.33/1.79    spl15_2 <=> r1_yellow_0(sK9,sK10)),
% 11.33/1.79    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 11.33/1.79  fof(f703,plain,(
% 11.33/1.79    sP7(sK14(sK9,sK10,sK11),sK11,sK9,sK10) | (spl15_1 | ~spl15_2 | ~spl15_5 | spl15_8)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f165,f150,f135,f130,f121])).
% 11.33/1.79  fof(f121,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (sP7(sK14(X0,X1,X2),X2,X0,X1) | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f73])).
% 11.33/1.79  fof(f73,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | (sP7(sK14(X0,X1,X2),X2,X0,X1) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))) | ~r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 11.33/1.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f43,f72])).
% 11.33/1.79  fof(f72,plain,(
% 11.33/1.79    ! [X2,X1,X0] : (? [X3] : (sP7(X3,X2,X0,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (sP7(sK14(X0,X1,X2),X2,X0,X1) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))))),
% 11.33/1.79    introduced(choice_axiom,[])).
% 11.33/1.79  fof(f43,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | ? [X3] : (sP7(X3,X2,X0,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 11.33/1.79    inference(definition_folding,[],[f27,f42])).
% 11.33/1.79  fof(f27,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | ? [X3] : ((r2_lattice3(X0,X1,X3) <~> r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 11.33/1.79    inference(flattening,[],[f26])).
% 11.33/1.79  fof(f26,plain,(
% 11.33/1.79    ! [X0] : (! [X1,X2] : (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | (? [X3] : ((r2_lattice3(X0,X1,X3) <~> r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 11.33/1.79    inference(ennf_transformation,[],[f10])).
% 11.33/1.79  fof(f10,axiom,(
% 11.33/1.79    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : ((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3))) & r1_yellow_0(X0,X1)) => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).
% 11.33/1.79  fof(f130,plain,(
% 11.33/1.79    k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11) | spl15_1),
% 11.33/1.79    inference(avatar_component_clause,[],[f128])).
% 11.33/1.79  fof(f135,plain,(
% 11.33/1.79    r1_yellow_0(sK9,sK10) | ~spl15_2),
% 11.33/1.79    inference(avatar_component_clause,[],[f133])).
% 11.33/1.79  fof(f631,plain,(
% 11.33/1.79    spl15_51 | spl15_1 | ~spl15_2 | ~spl15_5 | spl15_8),
% 11.33/1.79    inference(avatar_split_clause,[],[f626,f163,f148,f133,f128,f628])).
% 11.33/1.79  fof(f626,plain,(
% 11.33/1.79    m1_subset_1(sK14(sK9,sK10,sK11),u1_struct_0(sK9)) | (spl15_1 | ~spl15_2 | ~spl15_5 | spl15_8)),
% 11.33/1.79    inference(unit_resulting_resolution,[],[f165,f150,f135,f130,f120])).
% 11.33/1.79  fof(f120,plain,(
% 11.33/1.79    ( ! [X2,X0,X1] : (m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 11.33/1.79    inference(cnf_transformation,[],[f73])).
% 11.33/1.79  fof(f171,plain,(
% 11.33/1.79    spl15_9),
% 11.33/1.79    inference(avatar_split_clause,[],[f90,f168])).
% 11.33/1.79  fof(f90,plain,(
% 11.33/1.79    v1_xboole_0(k1_xboole_0)),
% 11.33/1.79    inference(cnf_transformation,[],[f1])).
% 11.33/1.79  fof(f1,axiom,(
% 11.33/1.79    v1_xboole_0(k1_xboole_0)),
% 11.33/1.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 11.33/1.79  fof(f166,plain,(
% 11.33/1.79    ~spl15_8),
% 11.33/1.79    inference(avatar_split_clause,[],[f79,f163])).
% 11.33/1.79  fof(f79,plain,(
% 11.33/1.79    ~v2_struct_0(sK9)),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f161,plain,(
% 11.33/1.79    spl15_7),
% 11.33/1.79    inference(avatar_split_clause,[],[f80,f158])).
% 11.33/1.79  fof(f80,plain,(
% 11.33/1.79    v3_orders_2(sK9)),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f151,plain,(
% 11.33/1.79    spl15_5),
% 11.33/1.79    inference(avatar_split_clause,[],[f82,f148])).
% 11.33/1.79  fof(f82,plain,(
% 11.33/1.79    l1_orders_2(sK9)),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f141,plain,(
% 11.33/1.79    spl15_3),
% 11.33/1.79    inference(avatar_split_clause,[],[f84,f138])).
% 11.33/1.79  fof(f84,plain,(
% 11.33/1.79    m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f136,plain,(
% 11.33/1.79    spl15_2),
% 11.33/1.79    inference(avatar_split_clause,[],[f88,f133])).
% 11.33/1.79  fof(f88,plain,(
% 11.33/1.79    r1_yellow_0(sK9,sK10)),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  fof(f131,plain,(
% 11.33/1.79    ~spl15_1),
% 11.33/1.79    inference(avatar_split_clause,[],[f89,f128])).
% 11.33/1.79  fof(f89,plain,(
% 11.33/1.79    k1_yellow_0(sK9,sK10) != k1_yellow_0(sK9,sK11)),
% 11.33/1.79    inference(cnf_transformation,[],[f52])).
% 11.33/1.79  % SZS output end Proof for theBenchmark
% 11.33/1.79  % (22065)------------------------------
% 11.33/1.79  % (22065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.33/1.79  % (22065)Termination reason: Refutation
% 11.33/1.79  
% 11.33/1.79  % (22065)Memory used [KB]: 36332
% 11.33/1.79  % (22065)Time elapsed: 1.372 s
% 11.33/1.79  % (22065)------------------------------
% 11.33/1.79  % (22065)------------------------------
% 11.33/1.79  % (22046)Success in time 1.438 s
%------------------------------------------------------------------------------
