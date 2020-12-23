%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 392 expanded)
%              Number of leaves         :   39 ( 152 expanded)
%              Depth                    :   12
%              Number of atoms          :  729 (2195 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23107)Termination reason: Refutation not found, incomplete strategy

% (23107)Memory used [KB]: 1663
% (23107)Time elapsed: 0.085 s
% (23107)------------------------------
% (23107)------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f102,f107,f112,f117,f127,f132,f141,f143,f149,f158,f169,f178,f185,f191,f215,f261,f269,f301,f310,f315,f328,f370,f380])).

fof(f380,plain,
    ( spl7_32
    | ~ spl7_33
    | ~ spl7_38 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl7_32
    | ~ spl7_33
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f377,f314])).

fof(f314,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl7_32
  <=> r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f377,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl7_33
    | ~ spl7_38 ),
    inference(resolution,[],[f369,f327])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl7_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f369,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl7_38
  <=> m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f370,plain,
    ( spl7_38
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f303,f298,f367])).

fof(f298,plain,
    ( spl7_30
  <=> r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f303,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(resolution,[],[f300,f183])).

fof(f183,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f78,f171])).

fof(f171,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f68,f162])).

fof(f162,plain,(
    ! [X0] : sK4(X0) = X0 ),
    inference(subsumption_resolution,[],[f160,f69])).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f160,plain,(
    ! [X0] :
      ( sK4(X0) = X0
      | v1_subset_1(sK4(X0),X0) ) ),
    inference(resolution,[],[f73,f68])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
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

fof(f300,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f298])).

fof(f328,plain,
    ( spl7_33
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f323,f308,f138,f109,f104,f99,f84,f326])).

fof(f84,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f99,plain,
    ( spl7_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f104,plain,
    ( spl7_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f109,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f138,plain,
    ( spl7_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f308,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f322,f86])).

fof(f86,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f321,f101])).

fof(f101,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f320,f106])).

fof(f106,plain,
    ( v1_yellow_0(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f319,f111])).

fof(f111,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f318,f139])).

fof(f139,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_31 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_31 ),
    inference(resolution,[],[f309,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f309,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f315,plain,
    ( ~ spl7_32
    | ~ spl7_10
    | spl7_15
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f306,f298,f166,f129,f312])).

fof(f129,plain,
    ( spl7_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f166,plain,
    ( spl7_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f306,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl7_10
    | spl7_15
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f305,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f305,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_15
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f304,f171])).

fof(f304,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_15
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f302,f167])).

fof(f167,plain,
    ( u1_struct_0(sK0) != sK1
    | spl7_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f302,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_30 ),
    inference(resolution,[],[f300,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
              | ~ r2_hidden(sK5(X0,X1,X2),X1) )
            & ( r2_hidden(sK5(X0,X1,X2),X2)
              | r2_hidden(sK5(X0,X1,X2),X1) )
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),X1) )
        & ( r2_hidden(sK5(X0,X1,X2),X2)
          | r2_hidden(sK5(X0,X1,X2),X1) )
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f310,plain,
    ( spl7_31
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f286,f267,f129,f124,f308])).

fof(f124,plain,
    ( spl7_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f267,plain,
    ( spl7_27
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f285,f131])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl7_9
    | ~ spl7_27 ),
    inference(resolution,[],[f268,f126])).

fof(f126,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f268,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f301,plain,
    ( spl7_30
    | spl7_15
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f279,f259,f202,f166,f298])).

fof(f202,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f259,plain,
    ( spl7_25
  <=> ! [X2] :
        ( r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2)
        | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f279,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl7_15
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f278,f203])).

fof(f203,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f202])).

fof(f278,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl7_15
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f275,f167])).

fof(f275,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl7_25 ),
    inference(resolution,[],[f260,f171])).

fof(f260,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1)
        | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2)
        | sK1 = X2 )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f259])).

fof(f269,plain,
    ( spl7_27
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f220,f109,f267])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl7_6 ),
    inference(resolution,[],[f219,f111])).

% (23104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f219,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f61,f78])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f38,plain,(
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

fof(f39,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f261,plain,
    ( spl7_25
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f213,f129,f259])).

fof(f213,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2)
        | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X2 )
    | ~ spl7_10 ),
    inference(resolution,[],[f76,f131])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f215,plain,
    ( spl7_17
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f194,f129,f202])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,u1_struct_0(sK0)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f131,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f191,plain,
    ( ~ spl7_11
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f188,f172])).

fof(f172,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f69,f162])).

fof(f188,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f136,f168])).

fof(f168,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f136,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f185,plain,
    ( u1_struct_0(sK0) != sK1
    | m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f178,plain,
    ( spl7_16
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f151,f146,f109,f175])).

fof(f175,plain,
    ( spl7_16
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f146,plain,
    ( spl7_13
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f151,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f150,f111])).

fof(f150,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_13 ),
    inference(superposition,[],[f70,f148])).

fof(f148,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f169,plain,
    ( spl7_15
    | ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f161,f134,f129,f166])).

fof(f161,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl7_10
    | spl7_11 ),
    inference(subsumption_resolution,[],[f159,f135])).

fof(f135,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f159,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f73,f131])).

fof(f158,plain,
    ( ~ spl7_14
    | spl7_7
    | spl7_12 ),
    inference(avatar_split_clause,[],[f153,f138,f114,f155])).

fof(f155,plain,
    ( spl7_14
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f114,plain,
    ( spl7_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f153,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl7_7
    | spl7_12 ),
    inference(subsumption_resolution,[],[f152,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f152,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl7_12 ),
    inference(resolution,[],[f71,f140])).

fof(f140,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f149,plain,
    ( spl7_13
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f144,f109,f146])).

fof(f144,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(resolution,[],[f60,f111])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f143,plain,
    ( ~ spl7_11
    | spl7_12 ),
    inference(avatar_split_clause,[],[f142,f138,f134])).

fof(f142,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_12 ),
    inference(subsumption_resolution,[],[f59,f140])).

fof(f59,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f141,plain,
    ( spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f58,f138,f134])).

fof(f58,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f57,f129])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f56,f124])).

fof(f56,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f54,f114])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (23121)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (23111)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (23108)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (23110)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (23102)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (23107)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (23107)Refutation not found, incomplete strategy% (23107)------------------------------
% 0.21/0.50  % (23107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23102)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (23107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23107)Memory used [KB]: 1663
% 0.21/0.50  % (23107)Time elapsed: 0.085 s
% 0.21/0.50  % (23107)------------------------------
% 0.21/0.50  % (23107)------------------------------
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f87,f102,f107,f112,f117,f127,f132,f141,f143,f149,f158,f169,f178,f185,f191,f215,f261,f269,f301,f310,f315,f328,f370,f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    spl7_32 | ~spl7_33 | ~spl7_38),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f379])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    $false | (spl7_32 | ~spl7_33 | ~spl7_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f377,f314])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | spl7_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f312])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    spl7_32 <=> r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | (~spl7_33 | ~spl7_38)),
% 0.21/0.50    inference(resolution,[],[f369,f327])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl7_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f326])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    spl7_33 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl7_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    spl7_38 <=> m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl7_38 | ~spl7_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f303,f298,f367])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    spl7_30 <=> r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl7_30),
% 0.21/0.50    inference(resolution,[],[f300,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X1,X2) | m1_subset_1(X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f78,f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f68,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0] : (sK4(X0) = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(sK4(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0] : (sK4(X0) = X0 | v1_subset_1(sK4(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f73,f68])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl7_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f298])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    spl7_33 | spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_12 | ~spl7_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f323,f308,f138,f109,f104,f99,f84,f326])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl7_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl7_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl7_5 <=> v1_yellow_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl7_6 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl7_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    spl7_31 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_12 | ~spl7_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f322,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | v2_struct_0(sK0)) ) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_12 | ~spl7_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f321,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl7_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_12 | ~spl7_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    v1_yellow_0(sK0) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl7_6 | ~spl7_12 | ~spl7_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f319,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl7_12 | ~spl7_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f318,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl7_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl7_31),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f316])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl7_31),
% 0.21/0.50    inference(resolution,[],[f309,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | ~spl7_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f308])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    ~spl7_32 | ~spl7_10 | spl7_15 | ~spl7_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f306,f298,f166,f129,f312])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl7_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl7_15 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | (~spl7_10 | spl7_15 | ~spl7_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f305,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_15 | ~spl7_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f304,f171])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_15 | ~spl7_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f302,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    u1_struct_0(sK0) != sK1 | spl7_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f166])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_30),
% 0.21/0.50    inference(resolution,[],[f300,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    spl7_31 | ~spl7_9 | ~spl7_10 | ~spl7_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f286,f267,f129,f124,f308])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl7_9 <=> v13_waybel_0(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl7_27 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) ) | (~spl7_9 | ~spl7_10 | ~spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f131])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl7_9 | ~spl7_27)),
% 0.21/0.50    inference(resolution,[],[f268,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    v13_waybel_0(sK1,sK0) | ~spl7_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl7_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f267])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl7_30 | spl7_15 | ~spl7_17 | ~spl7_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f279,f259,f202,f166,f298])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl7_17 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    spl7_25 <=> ! [X2] : (r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2) | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (spl7_15 | ~spl7_17 | ~spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f278,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl7_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (spl7_15 | ~spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f275,f167])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl7_25),
% 0.21/0.50    inference(resolution,[],[f260,f171])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1) | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2) | sK1 = X2) ) | ~spl7_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f259])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl7_27 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f220,f109,f267])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f219,f111])).
% 0.21/0.50  % (23104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f78])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(rectify,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl7_25 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f213,f129,f259])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),X2) | r2_hidden(sK5(u1_struct_0(sK0),sK1,X2),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X2) ) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f76,f131])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    spl7_17 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f194,f129,f202])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,u1_struct_0(sK0))) ) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f131,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~spl7_11 | ~spl7_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    $false | (~spl7_11 | ~spl7_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f69,f162])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    v1_subset_1(sK1,sK1) | (~spl7_11 | ~spl7_15)),
% 0.21/0.50    inference(backward_demodulation,[],[f136,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~spl7_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f166])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl7_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    u1_struct_0(sK0) != sK1 | m1_subset_1(k3_yellow_0(sK0),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl7_16 | ~spl7_6 | ~spl7_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f151,f146,f109,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl7_16 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl7_13 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl7_6 | ~spl7_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f111])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl7_13),
% 0.21/0.50    inference(superposition,[],[f70,f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl7_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f146])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl7_15 | ~spl7_10 | spl7_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f161,f134,f129,f166])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | (~spl7_10 | spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl7_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f73,f131])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~spl7_14 | spl7_7 | spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f138,f114,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl7_14 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl7_7 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ~m1_subset_1(k3_yellow_0(sK0),sK1) | (spl7_7 | spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1) | spl7_12),
% 0.21/0.50    inference(resolution,[],[f71,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl7_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl7_13 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f109,f146])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f60,f111])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~spl7_11 | spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f142,f138,f134])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl7_12),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f140])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl7_11 | ~spl7_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f138,f134])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f129])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl7_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f124])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v13_waybel_0(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f114])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f109])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f104])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_yellow_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl7_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f99])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f84])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (23102)------------------------------
% 0.21/0.50  % (23102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23102)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (23102)Memory used [KB]: 6396
% 0.21/0.50  % (23102)Time elapsed: 0.093 s
% 0.21/0.50  % (23102)------------------------------
% 0.21/0.50  % (23102)------------------------------
% 0.21/0.50  % (23099)Success in time 0.143 s
%------------------------------------------------------------------------------
