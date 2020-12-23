%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 405 expanded)
%              Number of leaves         :   43 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  919 (2380 expanded)
%              Number of equality atoms :   49 (  89 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1019,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f152,f157,f162,f172,f208,f254,f287,f288,f298,f316,f345,f418,f511,f630,f1014])).

fof(f1014,plain,
    ( ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_15
    | ~ spl8_18
    | spl8_22
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_15
    | ~ spl8_18
    | spl8_22
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f1003,f735])).

fof(f735,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl8_8
    | spl8_15
    | spl8_22 ),
    inference(subsumption_resolution,[],[f734,f161])).

fof(f161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f734,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | spl8_15
    | spl8_22 ),
    inference(subsumption_resolution,[],[f733,f179])).

fof(f179,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f119,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f733,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | spl8_15
    | spl8_22 ),
    inference(subsumption_resolution,[],[f732,f257])).

fof(f257,plain,
    ( u1_struct_0(sK0) != sK1
    | spl8_15 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl8_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f732,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | spl8_22 ),
    inference(duplicate_literal_removal,[],[f728])).

fof(f728,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK1
    | ~ r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | spl8_22 ),
    inference(resolution,[],[f440,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).

fof(f68,plain,(
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

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f440,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
        | sK1 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_8
    | spl8_22 ),
    inference(subsumption_resolution,[],[f439,f417])).

fof(f417,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl8_22
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f214,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f214,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl8_8 ),
    inference(resolution,[],[f107,f161])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1003,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_33 ),
    inference(resolution,[],[f714,f629])).

fof(f629,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl8_33
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f714,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f713,f423])).

fof(f423,plain,
    ( ! [X8] :
        ( r2_lattice3(sK0,k1_xboole_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(resolution,[],[f211,f163])).

fof(f163,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f156,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f156,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f97,f141])).

fof(f141,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f97,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f713,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f712,f170])).

fof(f170,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_10
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f712,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f708])).

fof(f708,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(resolution,[],[f459,f336])).

fof(f336,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f335,f141])).

fof(f335,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f329,f207])).

fof(f207,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl8_12
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f329,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_18 ),
    inference(superposition,[],[f122,f315])).

fof(f315,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl8_18
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f116,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f459,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f458,f161])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f233,f151])).

fof(f151,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f232,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f84,f141])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f630,plain,
    ( spl8_33
    | ~ spl8_8
    | spl8_15 ),
    inference(avatar_split_clause,[],[f373,f256,f159,f627])).

fof(f373,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_8
    | spl8_15 ),
    inference(unit_resulting_resolution,[],[f257,f161,f179,f107])).

fof(f511,plain,
    ( spl8_16
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f338,f313,f139,f279])).

fof(f279,plain,
    ( spl8_16
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f338,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f331,f141])).

fof(f331,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_18 ),
    inference(superposition,[],[f102,f315])).

fof(f418,plain,
    ( ~ spl8_22
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f362,f284,f415])).

fof(f284,plain,
    ( spl8_17
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f362,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f286,f100])).

fof(f286,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f284])).

fof(f345,plain,
    ( spl8_10
    | ~ spl8_8
    | spl8_15 ),
    inference(avatar_split_clause,[],[f344,f256,f159,f169])).

fof(f344,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_8
    | spl8_15 ),
    inference(subsumption_resolution,[],[f81,f343])).

fof(f343,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8
    | spl8_15 ),
    inference(subsumption_resolution,[],[f197,f257])).

fof(f197,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(resolution,[],[f105,f161])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f81,plain,
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
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
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
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
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
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
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
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
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
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
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
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f316,plain,
    ( spl8_18
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f182,f139,f313])).

fof(f182,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f141,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f298,plain,
    ( ~ spl8_9
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f290,f181])).

fof(f181,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f118,f179])).

fof(f118,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f290,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(superposition,[],[f167,f258])).

fof(f258,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f256])).

fof(f167,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_9
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f288,plain,
    ( u1_struct_0(sK0) != sK1
    | m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f287,plain,
    ( spl8_17
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f262,f169,f159,f284])).

fof(f262,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f161,f170,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f254,plain,
    ( ~ spl8_14
    | spl8_5
    | spl8_10 ),
    inference(avatar_split_clause,[],[f190,f169,f144,f251])).

fof(f251,plain,
    ( spl8_14
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f144,plain,
    ( spl8_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f190,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl8_5
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f171,f146,f103])).

fof(f146,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f171,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f208,plain,
    ( spl8_12
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f201,f139,f134,f129,f124,f205])).

fof(f124,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f129,plain,
    ( spl8_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f134,plain,
    ( spl8_3
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f201,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f126,f131,f136,f141,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f136,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f131,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f126,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f172,plain,
    ( spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f80,f169,f165])).

fof(f80,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f162,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f79,f159])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f157,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f82,f154])).

fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f152,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f78,f149])).

fof(f78,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f147,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f77,f144])).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f142,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f76,f139])).

fof(f76,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f137,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f75,f134])).

fof(f75,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f132,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f74,f129])).

fof(f74,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f127,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f73,f124])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (31925)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.47  % (31912)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (31933)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.48  % (31920)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (31911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (31916)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (31930)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.49  % (31922)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (31910)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (31914)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.50  % (31928)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % (31915)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.50  % (31913)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (31909)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (31914)Refutation not found, incomplete strategy% (31914)------------------------------
% 0.19/0.51  % (31914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (31914)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (31914)Memory used [KB]: 10618
% 0.19/0.51  % (31914)Time elapsed: 0.067 s
% 0.19/0.51  % (31914)------------------------------
% 0.19/0.51  % (31914)------------------------------
% 0.19/0.51  % (31926)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.51  % (31924)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.51  % (31908)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (31918)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.51  % (31908)Refutation not found, incomplete strategy% (31908)------------------------------
% 0.19/0.51  % (31908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (31908)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (31908)Memory used [KB]: 10618
% 0.19/0.51  % (31908)Time elapsed: 0.111 s
% 0.19/0.51  % (31908)------------------------------
% 0.19/0.51  % (31908)------------------------------
% 0.19/0.52  % (31915)Refutation not found, incomplete strategy% (31915)------------------------------
% 0.19/0.52  % (31915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (31915)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (31915)Memory used [KB]: 1791
% 0.19/0.52  % (31915)Time elapsed: 0.112 s
% 0.19/0.52  % (31915)------------------------------
% 0.19/0.52  % (31915)------------------------------
% 0.19/0.52  % (31927)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.52  % (31929)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.52  % (31919)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.52  % (31917)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.52  % (31931)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.53  % (31921)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.54  % (31923)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.54  % (31932)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.56  % (31931)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f1019,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f152,f157,f162,f172,f208,f254,f287,f288,f298,f316,f345,f418,f511,f630,f1014])).
% 0.19/0.56  fof(f1014,plain,(
% 0.19/0.56    ~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | spl8_15 | ~spl8_18 | spl8_22 | ~spl8_33),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f1013])).
% 0.19/0.56  fof(f1013,plain,(
% 0.19/0.56    $false | (~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | spl8_15 | ~spl8_18 | spl8_22 | ~spl8_33)),
% 0.19/0.56    inference(subsumption_resolution,[],[f1003,f735])).
% 0.19/0.56  fof(f735,plain,(
% 0.19/0.56    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | (~spl8_8 | spl8_15 | spl8_22)),
% 0.19/0.56    inference(subsumption_resolution,[],[f734,f161])).
% 0.19/0.56  fof(f161,plain,(
% 0.19/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_8),
% 0.19/0.56    inference(avatar_component_clause,[],[f159])).
% 0.19/0.56  fof(f159,plain,(
% 0.19/0.56    spl8_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.19/0.56  fof(f734,plain,(
% 0.19/0.56    ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_8 | spl8_15 | spl8_22)),
% 0.19/0.56    inference(subsumption_resolution,[],[f733,f179])).
% 0.19/0.56  fof(f179,plain,(
% 0.19/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f119,f114])).
% 0.19/0.56  fof(f114,plain,(
% 0.19/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f72])).
% 0.19/0.56  fof(f72,plain,(
% 0.19/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.56    inference(nnf_transformation,[],[f7])).
% 0.19/0.56  fof(f7,axiom,(
% 0.19/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.56  fof(f119,plain,(
% 0.19/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.56    inference(equality_resolution,[],[f111])).
% 0.19/0.56  fof(f111,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f71])).
% 0.19/0.56  fof(f71,plain,(
% 0.19/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.56    inference(flattening,[],[f70])).
% 1.61/0.56  fof(f70,plain,(
% 1.61/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.56    inference(nnf_transformation,[],[f3])).
% 1.61/0.56  fof(f3,axiom,(
% 1.61/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.56  fof(f733,plain,(
% 1.61/0.56    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_8 | spl8_15 | spl8_22)),
% 1.61/0.56    inference(subsumption_resolution,[],[f732,f257])).
% 1.61/0.56  fof(f257,plain,(
% 1.61/0.56    u1_struct_0(sK0) != sK1 | spl8_15),
% 1.61/0.56    inference(avatar_component_clause,[],[f256])).
% 1.61/0.56  fof(f256,plain,(
% 1.61/0.56    spl8_15 <=> u1_struct_0(sK0) = sK1),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.61/0.56  fof(f732,plain,(
% 1.61/0.56    u1_struct_0(sK0) = sK1 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_8 | spl8_22)),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f728])).
% 1.61/0.56  fof(f728,plain,(
% 1.61/0.56    u1_struct_0(sK0) = sK1 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK1 | ~r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_8 | spl8_22)),
% 1.61/0.56    inference(resolution,[],[f440,f109])).
% 1.61/0.56  fof(f109,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK7(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f69])).
% 1.61/0.56  fof(f69,plain,(
% 1.61/0.56    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(sK7(X0,X1,X2),X1)) & (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).
% 1.61/0.56  fof(f68,plain,(
% 1.61/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(sK7(X0,X1,X2),X1)) & (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),X0)))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f67,plain,(
% 1.61/0.56    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(flattening,[],[f66])).
% 1.61/0.56  fof(f66,plain,(
% 1.61/0.56    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(nnf_transformation,[],[f39])).
% 1.61/0.56  fof(f39,plain,(
% 1.61/0.56    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(flattening,[],[f38])).
% 1.61/0.56  fof(f38,plain,(
% 1.61/0.56    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f5])).
% 1.61/0.56  fof(f5,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.61/0.56  fof(f440,plain,(
% 1.61/0.56    ( ! [X0] : (r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl8_8 | spl8_22)),
% 1.61/0.56    inference(subsumption_resolution,[],[f439,f417])).
% 1.61/0.56  fof(f417,plain,(
% 1.61/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | spl8_22),
% 1.61/0.56    inference(avatar_component_clause,[],[f415])).
% 1.61/0.56  fof(f415,plain,(
% 1.61/0.56    spl8_22 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.61/0.56  fof(f439,plain,(
% 1.61/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))) ) | ~spl8_8),
% 1.61/0.56    inference(resolution,[],[f214,f103])).
% 1.61/0.56  fof(f103,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f35])).
% 1.61/0.56  fof(f35,plain,(
% 1.61/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.61/0.56    inference(flattening,[],[f34])).
% 1.61/0.56  fof(f34,plain,(
% 1.61/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.61/0.56    inference(ennf_transformation,[],[f6])).
% 1.61/0.56  fof(f6,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.61/0.56  fof(f214,plain,(
% 1.61/0.56    ( ! [X0] : (m1_subset_1(sK7(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | ~spl8_8),
% 1.61/0.56    inference(resolution,[],[f107,f161])).
% 1.61/0.56  fof(f107,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK7(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.61/0.56    inference(cnf_transformation,[],[f69])).
% 1.61/0.56  fof(f1003,plain,(
% 1.61/0.56    r2_hidden(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | (~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_18 | ~spl8_33)),
% 1.61/0.56    inference(resolution,[],[f714,f629])).
% 1.61/0.56  fof(f629,plain,(
% 1.61/0.56    m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl8_33),
% 1.61/0.56    inference(avatar_component_clause,[],[f627])).
% 1.61/0.56  fof(f627,plain,(
% 1.61/0.56    spl8_33 <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.61/0.56  fof(f714,plain,(
% 1.61/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(subsumption_resolution,[],[f713,f423])).
% 1.61/0.56  fof(f423,plain,(
% 1.61/0.56    ( ! [X8] : (r2_lattice3(sK0,k1_xboole_0,X8) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_7)),
% 1.61/0.56    inference(resolution,[],[f211,f163])).
% 1.61/0.56  fof(f163,plain,(
% 1.61/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_7),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f156,f100])).
% 1.61/0.56  fof(f100,plain,(
% 1.61/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f64])).
% 1.61/0.56  fof(f64,plain,(
% 1.61/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f63])).
% 1.61/0.56  fof(f63,plain,(
% 1.61/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f62,plain,(
% 1.61/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.56    inference(rectify,[],[f61])).
% 1.61/0.56  fof(f61,plain,(
% 1.61/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.56    inference(nnf_transformation,[],[f1])).
% 1.61/0.56  fof(f1,axiom,(
% 1.61/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.61/0.56  fof(f156,plain,(
% 1.61/0.56    v1_xboole_0(k1_xboole_0) | ~spl8_7),
% 1.61/0.56    inference(avatar_component_clause,[],[f154])).
% 1.61/0.56  fof(f154,plain,(
% 1.61/0.56    spl8_7 <=> v1_xboole_0(k1_xboole_0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.61/0.56  fof(f211,plain,(
% 1.61/0.56    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_4),
% 1.61/0.56    inference(resolution,[],[f97,f141])).
% 1.61/0.56  fof(f141,plain,(
% 1.61/0.56    l1_orders_2(sK0) | ~spl8_4),
% 1.61/0.56    inference(avatar_component_clause,[],[f139])).
% 1.61/0.56  fof(f139,plain,(
% 1.61/0.56    spl8_4 <=> l1_orders_2(sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.61/0.56  fof(f97,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f60])).
% 1.61/0.56  fof(f60,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).
% 1.61/0.56  fof(f59,plain,(
% 1.61/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f58,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(rectify,[],[f57])).
% 1.61/0.56  fof(f57,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(nnf_transformation,[],[f30])).
% 1.61/0.56  fof(f30,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f29])).
% 1.61/0.56  fof(f29,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f9])).
% 1.61/0.56  fof(f9,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.61/0.56  fof(f713,plain,(
% 1.61/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0)) ) | (~spl8_4 | ~spl8_6 | ~spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(subsumption_resolution,[],[f712,f170])).
% 1.61/0.56  fof(f170,plain,(
% 1.61/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_10),
% 1.61/0.56    inference(avatar_component_clause,[],[f169])).
% 1.61/0.56  fof(f169,plain,(
% 1.61/0.56    spl8_10 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.61/0.56  fof(f712,plain,(
% 1.61/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0)) ) | (~spl8_4 | ~spl8_6 | ~spl8_8 | ~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f708])).
% 1.61/0.56  fof(f708,plain,(
% 1.61/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_6 | ~spl8_8 | ~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(resolution,[],[f459,f336])).
% 1.61/0.56  fof(f336,plain,(
% 1.61/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(subsumption_resolution,[],[f335,f141])).
% 1.61/0.56  fof(f335,plain,(
% 1.61/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (~spl8_12 | ~spl8_18)),
% 1.61/0.56    inference(subsumption_resolution,[],[f329,f207])).
% 1.61/0.56  fof(f207,plain,(
% 1.61/0.56    r1_yellow_0(sK0,k1_xboole_0) | ~spl8_12),
% 1.61/0.56    inference(avatar_component_clause,[],[f205])).
% 1.61/0.56  fof(f205,plain,(
% 1.61/0.56    spl8_12 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.61/0.56  fof(f329,plain,(
% 1.61/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_18),
% 1.61/0.56    inference(superposition,[],[f122,f315])).
% 1.61/0.56  fof(f315,plain,(
% 1.61/0.56    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_18),
% 1.61/0.56    inference(avatar_component_clause,[],[f313])).
% 1.61/0.56  fof(f313,plain,(
% 1.61/0.56    spl8_18 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.61/0.56  fof(f122,plain,(
% 1.61/0.56    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f116,f102])).
% 1.61/0.56  fof(f102,plain,(
% 1.61/0.56    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f33])).
% 1.61/0.56  fof(f33,plain,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f12])).
% 1.61/0.56  fof(f12,axiom,(
% 1.61/0.56    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.61/0.56  fof(f116,plain,(
% 1.61/0.56    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(equality_resolution,[],[f91])).
% 1.61/0.56  fof(f91,plain,(
% 1.61/0.56    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f56])).
% 1.61/0.56  fof(f56,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 1.61/0.56  fof(f55,plain,(
% 1.61/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f54,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(rectify,[],[f53])).
% 1.61/0.56  fof(f53,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f52])).
% 1.61/0.56  fof(f52,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(nnf_transformation,[],[f28])).
% 1.61/0.56  fof(f28,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f27])).
% 1.61/0.56  fof(f27,plain,(
% 1.61/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f11])).
% 1.61/0.56  fof(f11,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.61/0.56  fof(f459,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | (~spl8_4 | ~spl8_6 | ~spl8_8)),
% 1.61/0.56    inference(subsumption_resolution,[],[f458,f161])).
% 1.61/0.56  fof(f458,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl8_4 | ~spl8_6)),
% 1.61/0.56    inference(resolution,[],[f233,f151])).
% 1.61/0.56  fof(f151,plain,(
% 1.61/0.56    v13_waybel_0(sK1,sK0) | ~spl8_6),
% 1.61/0.56    inference(avatar_component_clause,[],[f149])).
% 1.61/0.56  fof(f149,plain,(
% 1.61/0.56    spl8_6 <=> v13_waybel_0(sK1,sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.61/0.56  fof(f233,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_4),
% 1.61/0.56    inference(subsumption_resolution,[],[f232,f115])).
% 1.61/0.56  fof(f115,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f41])).
% 1.61/0.56  fof(f41,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/0.56    inference(flattening,[],[f40])).
% 1.61/0.56  fof(f40,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.61/0.56    inference(ennf_transformation,[],[f8])).
% 1.61/0.56  fof(f8,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.61/0.56  fof(f232,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_4),
% 1.61/0.56    inference(resolution,[],[f84,f141])).
% 1.61/0.56  fof(f84,plain,(
% 1.61/0.56    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f51])).
% 1.61/0.56  fof(f51,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).
% 1.61/0.56  fof(f49,plain,(
% 1.61/0.56    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f50,plain,(
% 1.61/0.56    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f48,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(rectify,[],[f47])).
% 1.61/0.56  fof(f47,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(nnf_transformation,[],[f26])).
% 1.61/0.56  fof(f26,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f25])).
% 1.61/0.56  fof(f25,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f14])).
% 1.61/0.56  fof(f14,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.61/0.56  fof(f630,plain,(
% 1.61/0.56    spl8_33 | ~spl8_8 | spl8_15),
% 1.61/0.56    inference(avatar_split_clause,[],[f373,f256,f159,f627])).
% 1.61/0.56  fof(f373,plain,(
% 1.61/0.56    m1_subset_1(sK7(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl8_8 | spl8_15)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f257,f161,f179,f107])).
% 1.61/0.56  fof(f511,plain,(
% 1.61/0.56    spl8_16 | ~spl8_4 | ~spl8_18),
% 1.61/0.56    inference(avatar_split_clause,[],[f338,f313,f139,f279])).
% 1.61/0.56  fof(f279,plain,(
% 1.61/0.56    spl8_16 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.61/0.56  fof(f338,plain,(
% 1.61/0.56    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl8_4 | ~spl8_18)),
% 1.61/0.56    inference(subsumption_resolution,[],[f331,f141])).
% 1.61/0.56  fof(f331,plain,(
% 1.61/0.56    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl8_18),
% 1.61/0.56    inference(superposition,[],[f102,f315])).
% 1.61/0.56  fof(f418,plain,(
% 1.61/0.56    ~spl8_22 | ~spl8_17),
% 1.61/0.56    inference(avatar_split_clause,[],[f362,f284,f415])).
% 1.61/0.56  fof(f284,plain,(
% 1.61/0.56    spl8_17 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.61/0.56  fof(f362,plain,(
% 1.61/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl8_17),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f286,f100])).
% 1.61/0.56  fof(f286,plain,(
% 1.61/0.56    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_17),
% 1.61/0.56    inference(avatar_component_clause,[],[f284])).
% 1.61/0.56  fof(f345,plain,(
% 1.61/0.56    spl8_10 | ~spl8_8 | spl8_15),
% 1.61/0.56    inference(avatar_split_clause,[],[f344,f256,f159,f169])).
% 1.61/0.56  fof(f344,plain,(
% 1.61/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | (~spl8_8 | spl8_15)),
% 1.61/0.56    inference(subsumption_resolution,[],[f81,f343])).
% 1.61/0.56  fof(f343,plain,(
% 1.61/0.56    v1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_8 | spl8_15)),
% 1.61/0.56    inference(subsumption_resolution,[],[f197,f257])).
% 1.61/0.56  fof(f197,plain,(
% 1.61/0.56    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_8),
% 1.61/0.56    inference(resolution,[],[f105,f161])).
% 1.61/0.56  fof(f105,plain,(
% 1.61/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f65])).
% 1.61/0.56  fof(f65,plain,(
% 1.61/0.56    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(nnf_transformation,[],[f36])).
% 1.61/0.56  fof(f36,plain,(
% 1.61/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f15])).
% 1.61/0.56  fof(f15,axiom,(
% 1.61/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.61/0.56  fof(f81,plain,(
% 1.61/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.61/0.56    inference(cnf_transformation,[],[f46])).
% 1.61/0.56  fof(f46,plain,(
% 1.61/0.56    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 1.61/0.56  fof(f44,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f45,plain,(
% 1.61/0.56    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f43,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.61/0.56    inference(flattening,[],[f42])).
% 1.61/0.56  fof(f42,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.61/0.56    inference(nnf_transformation,[],[f23])).
% 1.61/0.56  fof(f23,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.61/0.56    inference(flattening,[],[f22])).
% 1.61/0.56  fof(f22,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f20])).
% 1.61/0.56  fof(f20,plain,(
% 1.61/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.61/0.56    inference(pure_predicate_removal,[],[f19])).
% 1.61/0.56  fof(f19,plain,(
% 1.61/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.61/0.56    inference(pure_predicate_removal,[],[f18])).
% 1.61/0.56  fof(f18,plain,(
% 1.61/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.61/0.56    inference(pure_predicate_removal,[],[f17])).
% 1.61/0.56  fof(f17,negated_conjecture,(
% 1.61/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.61/0.56    inference(negated_conjecture,[],[f16])).
% 1.61/0.56  fof(f16,conjecture,(
% 1.61/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.61/0.56  fof(f316,plain,(
% 1.61/0.56    spl8_18 | ~spl8_4),
% 1.61/0.56    inference(avatar_split_clause,[],[f182,f139,f313])).
% 1.61/0.56  fof(f182,plain,(
% 1.61/0.56    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_4),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f141,f83])).
% 1.61/0.56  fof(f83,plain,(
% 1.61/0.56    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f24])).
% 1.61/0.56  fof(f24,plain,(
% 1.61/0.56    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f10])).
% 1.61/0.56  fof(f10,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.61/0.56  fof(f298,plain,(
% 1.61/0.56    ~spl8_9 | ~spl8_15),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f297])).
% 1.61/0.56  fof(f297,plain,(
% 1.61/0.56    $false | (~spl8_9 | ~spl8_15)),
% 1.61/0.56    inference(subsumption_resolution,[],[f290,f181])).
% 1.61/0.56  fof(f181,plain,(
% 1.61/0.56    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f118,f179])).
% 1.61/0.56  fof(f118,plain,(
% 1.61/0.56    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.61/0.56    inference(equality_resolution,[],[f104])).
% 1.61/0.56  fof(f104,plain,(
% 1.61/0.56    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f65])).
% 1.61/0.56  fof(f290,plain,(
% 1.61/0.56    v1_subset_1(sK1,sK1) | (~spl8_9 | ~spl8_15)),
% 1.61/0.56    inference(superposition,[],[f167,f258])).
% 1.61/0.56  fof(f258,plain,(
% 1.61/0.56    u1_struct_0(sK0) = sK1 | ~spl8_15),
% 1.61/0.56    inference(avatar_component_clause,[],[f256])).
% 1.61/0.56  fof(f167,plain,(
% 1.61/0.56    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_9),
% 1.61/0.56    inference(avatar_component_clause,[],[f165])).
% 1.61/0.56  fof(f165,plain,(
% 1.61/0.56    spl8_9 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.61/0.56  fof(f288,plain,(
% 1.61/0.56    u1_struct_0(sK0) != sK1 | m1_subset_1(k3_yellow_0(sK0),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.61/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.61/0.56  fof(f287,plain,(
% 1.61/0.56    spl8_17 | ~spl8_8 | ~spl8_10),
% 1.61/0.56    inference(avatar_split_clause,[],[f262,f169,f159,f284])).
% 1.61/0.56  fof(f262,plain,(
% 1.61/0.56    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl8_8 | ~spl8_10)),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f161,f170,f106])).
% 1.61/0.56  fof(f106,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f37])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.61/0.57  fof(f254,plain,(
% 1.61/0.57    ~spl8_14 | spl8_5 | spl8_10),
% 1.61/0.57    inference(avatar_split_clause,[],[f190,f169,f144,f251])).
% 1.61/0.57  fof(f251,plain,(
% 1.61/0.57    spl8_14 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.61/0.57  fof(f144,plain,(
% 1.61/0.57    spl8_5 <=> v1_xboole_0(sK1)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.61/0.57  fof(f190,plain,(
% 1.61/0.57    ~m1_subset_1(k3_yellow_0(sK0),sK1) | (spl8_5 | spl8_10)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f171,f146,f103])).
% 1.61/0.57  fof(f146,plain,(
% 1.61/0.57    ~v1_xboole_0(sK1) | spl8_5),
% 1.61/0.57    inference(avatar_component_clause,[],[f144])).
% 1.61/0.57  fof(f171,plain,(
% 1.61/0.57    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_10),
% 1.61/0.57    inference(avatar_component_clause,[],[f169])).
% 1.61/0.57  fof(f208,plain,(
% 1.61/0.57    spl8_12 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f201,f139,f134,f129,f124,f205])).
% 1.61/0.57  fof(f124,plain,(
% 1.61/0.57    spl8_1 <=> v2_struct_0(sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.61/0.57  fof(f129,plain,(
% 1.61/0.57    spl8_2 <=> v5_orders_2(sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.61/0.57  fof(f134,plain,(
% 1.61/0.57    spl8_3 <=> v1_yellow_0(sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.61/0.57  fof(f201,plain,(
% 1.61/0.57    r1_yellow_0(sK0,k1_xboole_0) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f126,f131,f136,f141,f99])).
% 1.61/0.57  fof(f99,plain,(
% 1.61/0.57    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f32])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.57    inference(flattening,[],[f31])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 1.61/0.57    inference(pure_predicate_removal,[],[f13])).
% 1.61/0.57  fof(f13,axiom,(
% 1.61/0.57    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.61/0.57  fof(f136,plain,(
% 1.61/0.57    v1_yellow_0(sK0) | ~spl8_3),
% 1.61/0.57    inference(avatar_component_clause,[],[f134])).
% 1.61/0.57  fof(f131,plain,(
% 1.61/0.57    v5_orders_2(sK0) | ~spl8_2),
% 1.61/0.57    inference(avatar_component_clause,[],[f129])).
% 1.61/0.57  fof(f126,plain,(
% 1.61/0.57    ~v2_struct_0(sK0) | spl8_1),
% 1.61/0.57    inference(avatar_component_clause,[],[f124])).
% 1.61/0.57  fof(f172,plain,(
% 1.61/0.57    spl8_9 | ~spl8_10),
% 1.61/0.57    inference(avatar_split_clause,[],[f80,f169,f165])).
% 1.61/0.57  fof(f80,plain,(
% 1.61/0.57    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f162,plain,(
% 1.61/0.57    spl8_8),
% 1.61/0.57    inference(avatar_split_clause,[],[f79,f159])).
% 1.61/0.57  fof(f79,plain,(
% 1.61/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f157,plain,(
% 1.61/0.57    spl8_7),
% 1.61/0.57    inference(avatar_split_clause,[],[f82,f154])).
% 1.61/0.57  fof(f82,plain,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    inference(cnf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.61/0.57  fof(f152,plain,(
% 1.61/0.57    spl8_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f78,f149])).
% 1.61/0.57  fof(f78,plain,(
% 1.61/0.57    v13_waybel_0(sK1,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f147,plain,(
% 1.61/0.57    ~spl8_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f77,f144])).
% 1.61/0.57  fof(f77,plain,(
% 1.61/0.57    ~v1_xboole_0(sK1)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f142,plain,(
% 1.61/0.57    spl8_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f76,f139])).
% 1.61/0.57  fof(f76,plain,(
% 1.61/0.57    l1_orders_2(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f137,plain,(
% 1.61/0.57    spl8_3),
% 1.61/0.57    inference(avatar_split_clause,[],[f75,f134])).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    v1_yellow_0(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f132,plain,(
% 1.61/0.57    spl8_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f74,f129])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    v5_orders_2(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  fof(f127,plain,(
% 1.61/0.57    ~spl8_1),
% 1.61/0.57    inference(avatar_split_clause,[],[f73,f124])).
% 1.61/0.57  fof(f73,plain,(
% 1.61/0.57    ~v2_struct_0(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f46])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (31931)------------------------------
% 1.61/0.57  % (31931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (31931)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (31931)Memory used [KB]: 11257
% 1.61/0.57  % (31931)Time elapsed: 0.169 s
% 1.61/0.57  % (31931)------------------------------
% 1.61/0.57  % (31931)------------------------------
% 1.61/0.57  % (31907)Success in time 0.214 s
%------------------------------------------------------------------------------
