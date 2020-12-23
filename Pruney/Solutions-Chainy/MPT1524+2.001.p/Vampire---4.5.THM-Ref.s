%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 298 expanded)
%              Number of leaves         :   30 ( 131 expanded)
%              Depth                    :    8
%              Number of atoms          :  590 (1291 expanded)
%              Number of equality atoms :   34 ( 143 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f64,f82,f88,f93,f101,f108,f112,f124,f127,f151,f155,f162,f177,f183,f256,f264,f283,f291,f312,f318,f330,f342,f350])).

% (14324)Refutation not found, incomplete strategy% (14324)------------------------------
% (14324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14324)Termination reason: Refutation not found, incomplete strategy

% (14324)Memory used [KB]: 6268
% (14324)Time elapsed: 0.117 s
% (14324)------------------------------
% (14324)------------------------------
% (14321)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f350,plain,
    ( ~ spl7_9
    | ~ spl7_12
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f73,f51,f105,f85])).

fof(f85,plain,
    ( spl7_9
  <=> r2_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f105,plain,
    ( spl7_12
  <=> r1_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f51,plain,
    ( spl7_3
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f73,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f72,f53])).

fof(f53,plain,
    ( sK3 = sK4
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f72,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK4)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f18,f53])).

fof(f18,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

% (14339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2,X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r1_lattice3(X0,X2,X3)
                           => r1_lattice3(X1,X2,X4) )
                          & ( r2_lattice3(X0,X2,X3)
                           => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f342,plain,
    ( ~ spl7_1
    | spl7_9
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f336,f316,f117,f61,f85,f41])).

fof(f41,plain,
    ( spl7_1
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f61,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f117,plain,
    ( spl7_14
  <=> u1_struct_0(sK1) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f316,plain,
    ( spl7_36
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r2_lattice3(sK1,X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f336,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_lattice3(sK1,sK2,sK3)
    | ~ l1_orders_2(sK1)
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(forward_demodulation,[],[f335,f119])).

fof(f119,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f335,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl7_36 ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_lattice3(sK1,sK2,sK3)
    | ~ spl7_36 ),
    inference(resolution,[],[f317,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r2_lattice3(sK1,X0,sK3) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f316])).

fof(f330,plain,
    ( ~ spl7_1
    | spl7_12
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f329,f310,f117,f61,f105,f41])).

fof(f310,plain,
    ( spl7_35
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f329,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK1,sK2,sK3)
    | ~ l1_orders_2(sK1)
    | ~ spl7_14
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f328,f119])).

fof(f328,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl7_35 ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_lattice3(sK1,sK2,sK3)
    | ~ spl7_35 ),
    inference(resolution,[],[f311,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f310])).

fof(f318,plain,
    ( ~ spl7_5
    | spl7_36
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f314,f289,f149,f316,f61])).

fof(f149,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f289,plain,
    ( spl7_34
  <=> ! [X2] :
        ( r2_lattice3(sK1,X2,sK3)
        | ~ r2_hidden(sK6(sK1,X2,sK3),sK2)
        | ~ m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r2_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0)) )
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r2_lattice3(sK1,X0,sK3)
        | r2_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0)) )
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(resolution,[],[f290,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f290,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK1,X2,sK3),sK2)
        | r2_lattice3(sK1,X2,sK3) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f289])).

fof(f312,plain,
    ( ~ spl7_5
    | spl7_35
    | ~ spl7_19
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f308,f262,f153,f310,f61])).

fof(f153,plain,
    ( spl7_19
  <=> ! [X3,X2] :
        ( m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f262,plain,
    ( spl7_31
  <=> ! [X2] :
        ( r1_lattice3(sK1,X2,sK3)
        | ~ r2_hidden(sK5(sK1,X2,sK3),sK2)
        | ~ m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0)) )
    | ~ spl7_19
    | ~ spl7_31 ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3)
        | r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0)) )
    | ~ spl7_19
    | ~ spl7_31 ),
    inference(resolution,[],[f263,f154])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f263,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK1,X2,sK3),sK2)
        | r1_lattice3(sK1,X2,sK3) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f262])).

fof(f291,plain,
    ( ~ spl7_5
    | spl7_34
    | ~ spl7_11
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f286,f281,f99,f289,f61])).

fof(f99,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f281,plain,
    ( spl7_33
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK1,X2,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f286,plain,
    ( ! [X2] :
        ( r2_lattice3(sK1,X2,sK3)
        | ~ m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK1,X2,sK3),sK2) )
    | ~ spl7_11
    | ~ spl7_33 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X2] :
        ( r2_lattice3(sK1,X2,sK3)
        | ~ m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK1,X2,sK3),sK2) )
    | ~ spl7_11
    | ~ spl7_33 ),
    inference(resolution,[],[f282,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f282,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,sK6(sK1,X2,X3),X3)
        | r2_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( ~ spl7_1
    | spl7_33
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f192,f181,f117,f281,f41])).

fof(f181,plain,
    ( spl7_22
  <=> ! [X1,X0] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f192,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK1,X2,X3),X3)
        | ~ m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r2_lattice3(sK1,X2,X3) )
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK1,X2,X3),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r2_lattice3(sK1,X2,X3) )
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f188,f119])).

fof(f188,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,sK6(sK1,X2,X3),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r2_lattice3(sK1,X2,X3) )
    | ~ spl7_22 ),
    inference(resolution,[],[f182,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f264,plain,
    ( ~ spl7_5
    | spl7_31
    | ~ spl7_13
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f259,f254,f110,f262,f61])).

fof(f110,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f254,plain,
    ( spl7_30
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK1,X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f259,plain,
    ( ! [X2] :
        ( r1_lattice3(sK1,X2,sK3)
        | ~ m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK1,X2,sK3),sK2) )
    | ~ spl7_13
    | ~ spl7_30 ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( ! [X2] :
        ( r1_lattice3(sK1,X2,sK3)
        | ~ m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK1,X2,sK3),sK2) )
    | ~ spl7_13
    | ~ spl7_30 ),
    inference(resolution,[],[f255,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK1,X1,X0))
        | r1_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f256,plain,
    ( ~ spl7_1
    | spl7_30
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f190,f181,f117,f254,f41])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK1,X1,X0))
        | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r1_lattice3(sK1,X1,X0) )
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK1,X1,X0))
        | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r1_lattice3(sK1,X1,X0) )
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f187,f119])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK1,X1,X0))
        | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r1_lattice3(sK1,X1,X0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f182,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f183,plain,
    ( ~ spl7_2
    | spl7_22
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f179,f175,f181,f46])).

fof(f46,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f175,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl7_21 ),
    inference(resolution,[],[f176,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (14327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( ~ spl7_1
    | spl7_21
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f169,f159,f117,f175,f41])).

fof(f159,plain,
    ( spl7_20
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f168,f119])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f165,f119])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl7_20 ),
    inference(superposition,[],[f28,f161])).

% (14328)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f161,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f162,plain,
    ( spl7_20
    | ~ spl7_15
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f157,f90,f121,f159])).

fof(f121,plain,
    ( spl7_15
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f90,plain,
    ( spl7_10
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f157,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl7_10 ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,
    ( ! [X4,X5] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
        | u1_orders_2(sK1) = X5 )
    | ~ spl7_10 ),
    inference(superposition,[],[f39,f92])).

fof(f92,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f155,plain,
    ( ~ spl7_1
    | spl7_19
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f132,f117,f153,f41])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r1_lattice3(sK1,X2,X3) )
    | ~ spl7_14 ),
    inference(superposition,[],[f31,f119])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f151,plain,
    ( ~ spl7_1
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f131,f117,f149,f41])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r2_lattice3(sK1,X0,X1) )
    | ~ spl7_14 ),
    inference(superposition,[],[f35,f119])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,
    ( ~ spl7_2
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl7_2
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f48,f123,f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f123,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f48,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f124,plain,
    ( spl7_14
    | ~ spl7_15
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f115,f90,f121,f117])).

fof(f115,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl7_10 ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | u1_struct_0(sK1) = X0 )
    | ~ spl7_10 ),
    inference(superposition,[],[f38,f92])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,
    ( ~ spl7_2
    | spl7_13
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f103,f75,f61,f110,f46])).

fof(f75,plain,
    ( spl7_7
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f108,plain,
    ( spl7_8
    | ~ spl7_12
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f102,f51,f105,f79])).

fof(f79,plain,
    ( spl7_8
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f102,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f20,f53])).

% (14337)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f20,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( ~ spl7_2
    | spl7_11
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f83,f79,f61,f99,f46])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f25,f90])).

fof(f25,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,
    ( spl7_7
    | ~ spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f71,f51,f85,f75])).

fof(f71,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f17,f53])).

fof(f17,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f19,f79,f75])).

fof(f19,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (14338)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (14342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (14325)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (14330)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (14334)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (14326)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14333)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (14320)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (14346)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (14322)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (14342)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f44,f49,f54,f64,f82,f88,f93,f101,f108,f112,f124,f127,f151,f155,f162,f177,f183,f256,f264,f283,f291,f312,f318,f330,f342,f350])).
% 0.21/0.52  % (14324)Refutation not found, incomplete strategy% (14324)------------------------------
% 0.21/0.52  % (14324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14324)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14324)Memory used [KB]: 6268
% 0.21/0.52  % (14324)Time elapsed: 0.117 s
% 0.21/0.52  % (14324)------------------------------
% 0.21/0.52  % (14324)------------------------------
% 0.21/0.52  % (14321)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ~spl7_9 | ~spl7_12 | ~spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f73,f51,f105,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl7_9 <=> r2_lattice3(sK1,sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl7_12 <=> r1_lattice3(sK1,sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl7_3 <=> sK3 = sK4),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~r1_lattice3(sK1,sK2,sK3) | ~r2_lattice3(sK1,sK2,sK3) | ~spl7_3),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    sK3 = sK4 | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK4) | ~spl7_3),
% 0.21/0.52    inference(forward_demodulation,[],[f18,f53])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ~r2_lattice3(sK1,sK2,sK4) | ~r1_lattice3(sK1,sK2,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  % (14339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2,X3] : (? [X4] : ((((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4)) & (r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4)) & (r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    ~spl7_1 | spl7_9 | ~spl7_5 | ~spl7_14 | ~spl7_36),
% 0.21/0.52    inference(avatar_split_clause,[],[f336,f316,f117,f61,f85,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl7_1 <=> l1_orders_2(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl7_5 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl7_14 <=> u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    spl7_36 <=> ! [X0] : (~r2_hidden(sK6(sK1,X0,sK3),sK2) | r2_lattice3(sK1,X0,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_lattice3(sK1,sK2,sK3) | ~l1_orders_2(sK1) | (~spl7_14 | ~spl7_36)),
% 0.21/0.52    inference(forward_demodulation,[],[f335,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0) | ~spl7_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    r2_lattice3(sK1,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~spl7_36),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f334])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    r2_lattice3(sK1,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,sK2,sK3) | ~spl7_36),
% 0.21/0.52    inference(resolution,[],[f317,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK1,X0,sK3),sK2) | r2_lattice3(sK1,X0,sK3)) ) | ~spl7_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f316])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    ~spl7_1 | spl7_12 | ~spl7_5 | ~spl7_14 | ~spl7_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f329,f310,f117,f61,f105,f41])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    spl7_35 <=> ! [X0] : (~r2_hidden(sK5(sK1,X0,sK3),sK2) | r1_lattice3(sK1,X0,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK1,sK2,sK3) | ~l1_orders_2(sK1) | (~spl7_14 | ~spl7_35)),
% 0.21/0.52    inference(forward_demodulation,[],[f328,f119])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    r1_lattice3(sK1,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~spl7_35),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f327])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    r1_lattice3(sK1,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r1_lattice3(sK1,sK2,sK3) | ~spl7_35),
% 0.21/0.52    inference(resolution,[],[f311,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5(sK1,X0,sK3),sK2) | r1_lattice3(sK1,X0,sK3)) ) | ~spl7_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f310])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    ~spl7_5 | spl7_36 | ~spl7_18 | ~spl7_34),
% 0.21/0.52    inference(avatar_split_clause,[],[f314,f289,f149,f316,f61])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl7_18 <=> ! [X1,X0] : (m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    spl7_34 <=> ! [X2] : (r2_lattice3(sK1,X2,sK3) | ~r2_hidden(sK6(sK1,X2,sK3),sK2) | ~m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK1,X0,sK3),sK2) | r2_lattice3(sK1,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0))) ) | (~spl7_18 | ~spl7_34)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK1,X0,sK3),sK2) | r2_lattice3(sK1,X0,sK3) | r2_lattice3(sK1,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0))) ) | (~spl7_18 | ~spl7_34)),
% 0.21/0.52    inference(resolution,[],[f290,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK6(sK1,X2,sK3),sK2) | r2_lattice3(sK1,X2,sK3)) ) | ~spl7_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f289])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ~spl7_5 | spl7_35 | ~spl7_19 | ~spl7_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f308,f262,f153,f310,f61])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl7_19 <=> ! [X3,X2] : (m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0)) | r1_lattice3(sK1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    spl7_31 <=> ! [X2] : (r1_lattice3(sK1,X2,sK3) | ~r2_hidden(sK5(sK1,X2,sK3),sK2) | ~m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5(sK1,X0,sK3),sK2) | r1_lattice3(sK1,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0))) ) | (~spl7_19 | ~spl7_31)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f307])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5(sK1,X0,sK3),sK2) | r1_lattice3(sK1,X0,sK3) | r1_lattice3(sK1,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0))) ) | (~spl7_19 | ~spl7_31)),
% 0.21/0.52    inference(resolution,[],[f263,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X2,X3] : (m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0)) | r1_lattice3(sK1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl7_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK1,X2,sK3),sK2) | r1_lattice3(sK1,X2,sK3)) ) | ~spl7_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f262])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ~spl7_5 | spl7_34 | ~spl7_11 | ~spl7_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f286,f281,f99,f289,f61])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl7_11 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK3) | ~r2_hidden(X0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    spl7_33 <=> ! [X3,X2] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK1,X2,X3) | ~m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK1,X2,X3),X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X2] : (r2_lattice3(sK1,X2,sK3) | ~m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_hidden(sK6(sK1,X2,sK3),sK2)) ) | (~spl7_11 | ~spl7_33)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f285])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    ( ! [X2] : (r2_lattice3(sK1,X2,sK3) | ~m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK6(sK1,X2,sK3),sK2)) ) | (~spl7_11 | ~spl7_33)),
% 0.21/0.52    inference(resolution,[],[f282,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl7_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_orders_2(sK0,sK6(sK1,X2,X3),X3) | r2_lattice3(sK1,X2,X3) | ~m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl7_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f281])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ~spl7_1 | spl7_33 | ~spl7_14 | ~spl7_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f192,f181,f117,f281,f41])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl7_22 <=> ! [X1,X0] : (r1_orders_2(sK1,X0,X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK1,X2,X3),X3) | ~m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,X2,X3)) ) | (~spl7_14 | ~spl7_22)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,X2,X3)) ) | (~spl7_14 | ~spl7_22)),
% 0.21/0.53    inference(forward_demodulation,[],[f188,f119])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_orders_2(sK0,sK6(sK1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,X2,X3)) ) | ~spl7_22),
% 0.21/0.53    inference(resolution,[],[f182,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_orders_2(sK1,X0,X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f181])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~spl7_5 | spl7_31 | ~spl7_13 | ~spl7_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f259,f254,f110,f262,f61])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl7_13 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,X0) | ~r2_hidden(X0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl7_30 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK1,X1,X0) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK1,X1,X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ( ! [X2] : (r1_lattice3(sK1,X2,sK3) | ~m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_hidden(sK5(sK1,X2,sK3),sK2)) ) | (~spl7_13 | ~spl7_30)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ( ! [X2] : (r1_lattice3(sK1,X2,sK3) | ~m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK1,X2,sK3),sK2)) ) | (~spl7_13 | ~spl7_30)),
% 0.21/0.53    inference(resolution,[],[f255,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl7_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK5(sK1,X1,X0)) | r1_lattice3(sK1,X1,X0) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f254])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ~spl7_1 | spl7_30 | ~spl7_14 | ~spl7_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f190,f181,f117,f254,f41])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK1,X1,X0)) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r1_lattice3(sK1,X1,X0)) ) | (~spl7_14 | ~spl7_22)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK1,X1,X0)) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r1_lattice3(sK1,X1,X0)) ) | (~spl7_14 | ~spl7_22)),
% 0.21/0.53    inference(forward_demodulation,[],[f187,f119])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK5(sK1,X1,X0)) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r1_lattice3(sK1,X1,X0)) ) | ~spl7_22),
% 0.21/0.53    inference(resolution,[],[f182,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ~spl7_2 | spl7_22 | ~spl7_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f179,f175,f181,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl7_2 <=> l1_orders_2(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl7_21 <=> ! [X1,X0] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_orders_2(sK0,X0,X1)) ) | ~spl7_21),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_orders_2(sK0,X0,X1)) ) | ~spl7_21),
% 0.21/0.53    inference(resolution,[],[f176,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  % (14327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f175])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~spl7_1 | spl7_21 | ~spl7_14 | ~spl7_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f169,f159,f117,f175,f41])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl7_20 <=> u1_orders_2(sK0) = u1_orders_2(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~l1_orders_2(sK1) | r1_orders_2(sK1,X0,X1)) ) | (~spl7_14 | ~spl7_20)),
% 0.21/0.53    inference(forward_demodulation,[],[f168,f119])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r1_orders_2(sK1,X0,X1)) ) | (~spl7_14 | ~spl7_20)),
% 0.21/0.53    inference(forward_demodulation,[],[f165,f119])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | r1_orders_2(sK1,X0,X1)) ) | ~spl7_20),
% 0.21/0.53    inference(superposition,[],[f28,f161])).
% 0.21/0.53  % (14328)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    u1_orders_2(sK0) = u1_orders_2(sK1) | ~spl7_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f159])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl7_20 | ~spl7_15 | ~spl7_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f157,f90,f121,f159])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl7_15 <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl7_10 <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_orders_2(sK0) = u1_orders_2(sK1) | ~spl7_10),
% 0.21/0.53    inference(equality_resolution,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X4,X5] : (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) | u1_orders_2(sK1) = X5) ) | ~spl7_10),
% 0.21/0.53    inference(superposition,[],[f39,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) | ~spl7_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | X1 = X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ~spl7_1 | spl7_19 | ~spl7_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f132,f117,f153,f41])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X2,X3] : (m1_subset_1(sK5(sK1,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r1_lattice3(sK1,X2,X3)) ) | ~spl7_14),
% 0.21/0.53    inference(superposition,[],[f31,f119])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~spl7_1 | spl7_18 | ~spl7_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f131,f117,f149,f41])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,X0,X1)) ) | ~spl7_14),
% 0.21/0.53    inference(superposition,[],[f35,f119])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~spl7_2 | spl7_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    $false | (~spl7_2 | spl7_15)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f48,f123,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | spl7_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    l1_orders_2(sK0) | ~spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f46])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl7_14 | ~spl7_15 | ~spl7_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f115,f90,f121,f117])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = u1_struct_0(sK0) | ~spl7_10),
% 0.21/0.53    inference(equality_resolution,[],[f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | u1_struct_0(sK1) = X0) ) | ~spl7_10),
% 0.21/0.53    inference(superposition,[],[f38,f92])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | X0 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~spl7_2 | spl7_13 | ~spl7_5 | ~spl7_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f103,f75,f61,f110,f46])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl7_7 <=> r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,sK3,X0) | ~l1_orders_2(sK0)) ) | ~spl7_7),
% 0.21/0.53    inference(resolution,[],[f77,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    r1_lattice3(sK0,sK2,sK3) | ~spl7_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl7_8 | ~spl7_12 | ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f102,f51,f105,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl7_8 <=> r2_lattice3(sK0,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~r1_lattice3(sK1,sK2,sK3) | r2_lattice3(sK0,sK2,sK3) | ~spl7_3),
% 0.21/0.53    inference(forward_demodulation,[],[f20,f53])).
% 0.21/0.53  % (14337)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl7_2 | spl7_11 | ~spl7_5 | ~spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f83,f79,f61,f99,f46])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | ~l1_orders_2(sK0)) ) | ~spl7_8),
% 0.21/0.53    inference(resolution,[],[f81,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    r2_lattice3(sK0,sK2,sK3) | ~spl7_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f79])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl7_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f90])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl7_7 | ~spl7_9 | ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f71,f51,f85,f75])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3) | ~spl7_3),
% 0.21/0.53    inference(forward_demodulation,[],[f17,f53])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ~r2_lattice3(sK1,sK2,sK4) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl7_7 | spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f19,f79,f75])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f61])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f51])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    sK3 = sK4),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f26,f46])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f24,f41])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    l1_orders_2(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14342)------------------------------
% 0.21/0.53  % (14342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14342)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14342)Memory used [KB]: 10874
% 0.21/0.53  % (14342)Time elapsed: 0.069 s
% 0.21/0.53  % (14342)------------------------------
% 0.21/0.53  % (14342)------------------------------
% 0.21/0.53  % (14340)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (14319)Success in time 0.175 s
%------------------------------------------------------------------------------
