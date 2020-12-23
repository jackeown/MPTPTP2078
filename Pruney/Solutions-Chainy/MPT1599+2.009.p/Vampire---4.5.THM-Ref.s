%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 294 expanded)
%              Number of leaves         :   32 ( 127 expanded)
%              Depth                    :   11
%              Number of atoms          :  564 (1386 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f141,f177,f179,f191,f202,f204,f255,f329,f337,f354,f358,f373,f375,f424,f429,f1220,f1221,f1222])).

fof(f1222,plain,
    ( spl5_12
    | ~ spl5_148
    | ~ spl5_50
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1184,f421,f356,f929,f170])).

fof(f170,plain,
    ( spl5_12
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f929,plain,
    ( spl5_148
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f356,plain,
    ( spl5_50
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK1)
        | r1_tarski(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

% (5916)Refutation not found, incomplete strategy% (5916)------------------------------
% (5916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5928)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (5917)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (5921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f421,plain,
    ( spl5_56
  <=> r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1184,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl5_50
    | ~ spl5_56 ),
    inference(resolution,[],[f357,f423])).

fof(f423,plain,
    ( r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f421])).

fof(f357,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK1) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f356])).

fof(f1221,plain,
    ( spl5_13
    | ~ spl5_148
    | ~ spl5_52
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f1201,f426,f371,f929,f174])).

fof(f174,plain,
    ( spl5_13
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f371,plain,
    ( spl5_52
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK2)
        | r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f426,plain,
    ( spl5_57
  <=> r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f1201,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl5_52
    | ~ spl5_57 ),
    inference(resolution,[],[f372,f428])).

fof(f428,plain,
    ( r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f426])).

fof(f372,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK2) )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f371])).

fof(f1220,plain,
    ( ~ spl5_29
    | spl5_148 ),
    inference(avatar_contradiction_clause,[],[f1218])).

fof(f1218,plain,
    ( $false
    | ~ spl5_29
    | spl5_148 ),
    inference(resolution,[],[f931,f385])).

fof(f385,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl5_29 ),
    inference(resolution,[],[f254,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f254,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0)))
        | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_29
  <=> ! [X9] :
        ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f931,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | spl5_148 ),
    inference(avatar_component_clause,[],[f929])).

fof(f429,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_3
    | ~ spl5_48
    | ~ spl5_51
    | spl5_57
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f399,f253,f426,f367,f339,f97,f206,f93,f89])).

fof(f89,plain,
    ( spl5_1
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f93,plain,
    ( spl5_2
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f206,plain,
    ( spl5_18
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f97,plain,
    ( spl5_3
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f339,plain,
    ( spl5_48
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f367,plain,
    ( spl5_51
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f399,plain,
    ( r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_29 ),
    inference(resolution,[],[f385,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f424,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_3
    | ~ spl5_48
    | ~ spl5_51
    | spl5_56
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f398,f253,f421,f367,f339,f97,f206,f93,f89])).

fof(f398,plain,
    ( r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_29 ),
    inference(resolution,[],[f385,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f375,plain,(
    spl5_51 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl5_51 ),
    inference(resolution,[],[f369,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f369,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | spl5_51 ),
    inference(avatar_component_clause,[],[f367])).

fof(f373,plain,
    ( spl5_1
    | ~ spl5_19
    | ~ spl5_3
    | ~ spl5_51
    | spl5_52
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f364,f189,f371,f367,f97,f213,f89])).

fof(f213,plain,
    ( spl5_19
  <=> v3_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f189,plain,
    ( spl5_16
  <=> ! [X1] :
        ( r1_tarski(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r3_orders_2(k2_yellow_1(sK0),X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f364,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f190,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

% (5918)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f190,plain,
    ( ! [X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK2) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f358,plain,
    ( spl5_1
    | ~ spl5_19
    | ~ spl5_3
    | ~ spl5_48
    | spl5_50
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f348,f139,f356,f339,f97,f213,f89])).

fof(f139,plain,
    ( spl5_9
  <=> ! [X1] :
        ( r1_tarski(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r3_orders_2(k2_yellow_1(sK0),X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f140,f66])).

fof(f140,plain,
    ( ! [X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,sK1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f354,plain,(
    spl5_48 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl5_48 ),
    inference(resolution,[],[f341,f42])).

fof(f341,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f339])).

fof(f337,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f215,f46])).

fof(f46,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f215,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f213])).

fof(f329,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f208,f41])).

fof(f41,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f208,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f255,plain,
    ( ~ spl5_3
    | spl5_29 ),
    inference(avatar_split_clause,[],[f159,f253,f97])).

fof(f159,plain,(
    ! [X9] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f43,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f204,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f99,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f202,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f191,plain,
    ( spl5_7
    | spl5_16 ),
    inference(avatar_split_clause,[],[f151,f189,f131])).

fof(f131,plain,
    ( spl5_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f151,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK2)
      | ~ r3_orders_2(k2_yellow_1(sK0),X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f179,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f133,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f177,plain,
    ( ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f167,f174,f170])).

fof(f167,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f69,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f44,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f141,plain,
    ( spl5_7
    | spl5_9 ),
    inference(avatar_split_clause,[],[f114,f139,f131])).

fof(f114,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK1)
      | ~ r3_orders_2(k2_yellow_1(sK0),X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f42,f53])).

fof(f112,plain,
    ( ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f87,f89,f97])).

fof(f87,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5913)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (5905)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (5905)Refutation not found, incomplete strategy% (5905)------------------------------
% 0.21/0.51  % (5905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5905)Memory used [KB]: 1663
% 0.21/0.51  % (5905)Time elapsed: 0.093 s
% 0.21/0.51  % (5905)------------------------------
% 0.21/0.51  % (5905)------------------------------
% 0.21/0.51  % (5908)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (5913)Refutation not found, incomplete strategy% (5913)------------------------------
% 0.21/0.52  % (5913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5913)Memory used [KB]: 10746
% 0.21/0.52  % (5913)Time elapsed: 0.079 s
% 0.21/0.52  % (5913)------------------------------
% 0.21/0.52  % (5913)------------------------------
% 0.21/0.52  % (5930)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (5920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (5930)Refutation not found, incomplete strategy% (5930)------------------------------
% 0.21/0.52  % (5930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5930)Memory used [KB]: 6268
% 0.21/0.52  % (5930)Time elapsed: 0.081 s
% 0.21/0.52  % (5930)------------------------------
% 0.21/0.52  % (5930)------------------------------
% 0.21/0.52  % (5932)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (5923)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (5911)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5912)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (5915)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (5907)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5927)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (5907)Refutation not found, incomplete strategy% (5907)------------------------------
% 0.21/0.54  % (5907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5907)Memory used [KB]: 10746
% 0.21/0.54  % (5907)Time elapsed: 0.116 s
% 0.21/0.54  % (5907)------------------------------
% 0.21/0.54  % (5907)------------------------------
% 0.21/0.54  % (5906)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (5927)Refutation not found, incomplete strategy% (5927)------------------------------
% 0.21/0.54  % (5927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5927)Memory used [KB]: 10746
% 0.21/0.54  % (5927)Time elapsed: 0.107 s
% 0.21/0.54  % (5927)------------------------------
% 0.21/0.54  % (5927)------------------------------
% 0.21/0.54  % (5916)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5919)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (5910)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (5909)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (5931)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (5922)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (5926)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (5920)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (5914)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (5933)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (5934)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (5915)Refutation not found, incomplete strategy% (5915)------------------------------
% 0.21/0.55  % (5915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5915)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5915)Memory used [KB]: 10618
% 0.21/0.55  % (5915)Time elapsed: 0.144 s
% 0.21/0.55  % (5915)------------------------------
% 0.21/0.55  % (5915)------------------------------
% 0.21/0.55  % (5914)Refutation not found, incomplete strategy% (5914)------------------------------
% 0.21/0.55  % (5914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5914)Memory used [KB]: 10746
% 0.21/0.55  % (5914)Time elapsed: 0.142 s
% 0.21/0.55  % (5914)------------------------------
% 0.21/0.55  % (5914)------------------------------
% 0.21/0.55  % (5924)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (5922)Refutation not found, incomplete strategy% (5922)------------------------------
% 0.21/0.56  % (5922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5922)Memory used [KB]: 10618
% 0.21/0.56  % (5922)Time elapsed: 0.140 s
% 0.21/0.56  % (5922)------------------------------
% 0.21/0.56  % (5922)------------------------------
% 0.21/0.56  % (5925)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (5931)Refutation not found, incomplete strategy% (5931)------------------------------
% 0.21/0.56  % (5931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5931)Memory used [KB]: 10746
% 0.21/0.56  % (5931)Time elapsed: 0.139 s
% 0.21/0.56  % (5931)------------------------------
% 0.21/0.56  % (5931)------------------------------
% 0.21/0.56  % (5909)Refutation not found, incomplete strategy% (5909)------------------------------
% 0.21/0.56  % (5909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5909)Memory used [KB]: 6268
% 0.21/0.56  % (5909)Time elapsed: 0.138 s
% 0.21/0.56  % (5909)------------------------------
% 0.21/0.56  % (5909)------------------------------
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1237,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f112,f141,f177,f179,f191,f202,f204,f255,f329,f337,f354,f358,f373,f375,f424,f429,f1220,f1221,f1222])).
% 0.21/0.56  fof(f1222,plain,(
% 0.21/0.56    spl5_12 | ~spl5_148 | ~spl5_50 | ~spl5_56),
% 0.21/0.56    inference(avatar_split_clause,[],[f1184,f421,f356,f929,f170])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    spl5_12 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.56  fof(f929,plain,(
% 0.21/0.56    spl5_148 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).
% 0.21/0.56  fof(f356,plain,(
% 0.21/0.56    spl5_50 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK1) | r1_tarski(X1,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.21/0.56  % (5916)Refutation not found, incomplete strategy% (5916)------------------------------
% 0.21/0.56  % (5916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5928)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (5917)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (5921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.57  fof(f421,plain,(
% 1.53/0.57    spl5_56 <=> r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 1.53/0.57  fof(f1184,plain,(
% 1.53/0.57    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl5_50 | ~spl5_56)),
% 1.53/0.57    inference(resolution,[],[f357,f423])).
% 1.53/0.57  fof(f423,plain,(
% 1.53/0.57    r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl5_56),
% 1.53/0.57    inference(avatar_component_clause,[],[f421])).
% 1.53/0.57  fof(f357,plain,(
% 1.53/0.57    ( ! [X1] : (~r1_orders_2(k2_yellow_1(sK0),X1,sK1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK1)) ) | ~spl5_50),
% 1.53/0.57    inference(avatar_component_clause,[],[f356])).
% 1.53/0.57  fof(f1221,plain,(
% 1.53/0.57    spl5_13 | ~spl5_148 | ~spl5_52 | ~spl5_57),
% 1.53/0.57    inference(avatar_split_clause,[],[f1201,f426,f371,f929,f174])).
% 1.53/0.57  fof(f174,plain,(
% 1.53/0.57    spl5_13 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.53/0.57  fof(f371,plain,(
% 1.53/0.57    spl5_52 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK2) | r1_tarski(X1,sK2))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.53/0.57  fof(f426,plain,(
% 1.53/0.57    spl5_57 <=> r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 1.53/0.57  fof(f1201,plain,(
% 1.53/0.57    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl5_52 | ~spl5_57)),
% 1.53/0.57    inference(resolution,[],[f372,f428])).
% 1.53/0.57  fof(f428,plain,(
% 1.53/0.57    r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~spl5_57),
% 1.53/0.57    inference(avatar_component_clause,[],[f426])).
% 1.53/0.57  fof(f372,plain,(
% 1.53/0.57    ( ! [X1] : (~r1_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK2)) ) | ~spl5_52),
% 1.53/0.57    inference(avatar_component_clause,[],[f371])).
% 1.53/0.57  fof(f1220,plain,(
% 1.53/0.57    ~spl5_29 | spl5_148),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f1218])).
% 1.53/0.57  fof(f1218,plain,(
% 1.53/0.57    $false | (~spl5_29 | spl5_148)),
% 1.53/0.57    inference(resolution,[],[f931,f385])).
% 1.53/0.57  fof(f385,plain,(
% 1.53/0.57    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~spl5_29),
% 1.53/0.57    inference(resolution,[],[f254,f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 1.53/0.57    inference(flattening,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,negated_conjecture,(
% 1.53/0.57    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 1.53/0.57    inference(negated_conjecture,[],[f12])).
% 1.53/0.57  fof(f12,conjecture,(
% 1.53/0.57    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 1.53/0.57  fof(f254,plain,(
% 1.53/0.57    ( ! [X9] : (~m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl5_29),
% 1.53/0.57    inference(avatar_component_clause,[],[f253])).
% 1.53/0.57  fof(f253,plain,(
% 1.53/0.57    spl5_29 <=> ! [X9] : (m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.53/0.57  fof(f931,plain,(
% 1.53/0.57    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | spl5_148),
% 1.53/0.57    inference(avatar_component_clause,[],[f929])).
% 1.53/0.57  fof(f429,plain,(
% 1.53/0.57    spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_3 | ~spl5_48 | ~spl5_51 | spl5_57 | ~spl5_29),
% 1.53/0.57    inference(avatar_split_clause,[],[f399,f253,f426,f367,f339,f97,f206,f93,f89])).
% 1.53/0.57  fof(f89,plain,(
% 1.53/0.57    spl5_1 <=> v2_struct_0(k2_yellow_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.53/0.57  fof(f93,plain,(
% 1.53/0.57    spl5_2 <=> v5_orders_2(k2_yellow_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.53/0.57  fof(f206,plain,(
% 1.53/0.57    spl5_18 <=> v2_lattice3(k2_yellow_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.53/0.57  fof(f97,plain,(
% 1.53/0.57    spl5_3 <=> l1_orders_2(k2_yellow_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.53/0.57  fof(f339,plain,(
% 1.53/0.57    spl5_48 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.53/0.57  fof(f367,plain,(
% 1.53/0.57    spl5_51 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.53/0.57  fof(f399,plain,(
% 1.53/0.57    r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | ~spl5_29),
% 1.53/0.57    inference(resolution,[],[f385,f72])).
% 1.53/0.57  fof(f72,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f57])).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(rectify,[],[f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(nnf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 1.53/0.57  fof(f424,plain,(
% 1.53/0.57    spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_3 | ~spl5_48 | ~spl5_51 | spl5_56 | ~spl5_29),
% 1.53/0.57    inference(avatar_split_clause,[],[f398,f253,f421,f367,f339,f97,f206,f93,f89])).
% 1.53/0.57  fof(f398,plain,(
% 1.53/0.57    r1_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | ~spl5_29),
% 1.53/0.57    inference(resolution,[],[f385,f73])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f56])).
% 1.53/0.57  fof(f56,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f38])).
% 1.53/0.57  fof(f375,plain,(
% 1.53/0.57    spl5_51),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f374])).
% 1.53/0.57  fof(f374,plain,(
% 1.53/0.57    $false | spl5_51),
% 1.53/0.57    inference(resolution,[],[f369,f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f369,plain,(
% 1.53/0.57    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | spl5_51),
% 1.53/0.57    inference(avatar_component_clause,[],[f367])).
% 1.53/0.57  fof(f373,plain,(
% 1.53/0.57    spl5_1 | ~spl5_19 | ~spl5_3 | ~spl5_51 | spl5_52 | ~spl5_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f364,f189,f371,f367,f97,f213,f89])).
% 1.53/0.57  fof(f213,plain,(
% 1.53/0.57    spl5_19 <=> v3_orders_2(k2_yellow_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.53/0.57  fof(f189,plain,(
% 1.53/0.57    spl5_16 <=> ! [X1] : (r1_tarski(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~r3_orders_2(k2_yellow_1(sK0),X1,sK2))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.53/0.57  fof(f364,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl5_16),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f363])).
% 1.53/0.57  fof(f363,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl5_16),
% 1.53/0.57    inference(resolution,[],[f190,f66])).
% 1.53/0.57  fof(f66,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(nnf_transformation,[],[f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.57    inference(flattening,[],[f23])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.53/0.57  % (5918)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.57  fof(f190,plain,(
% 1.53/0.57    ( ! [X1] : (~r3_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK2)) ) | ~spl5_16),
% 1.53/0.57    inference(avatar_component_clause,[],[f189])).
% 1.53/0.57  fof(f358,plain,(
% 1.53/0.57    spl5_1 | ~spl5_19 | ~spl5_3 | ~spl5_48 | spl5_50 | ~spl5_9),
% 1.53/0.57    inference(avatar_split_clause,[],[f348,f139,f356,f339,f97,f213,f89])).
% 1.53/0.57  fof(f139,plain,(
% 1.53/0.57    spl5_9 <=> ! [X1] : (r1_tarski(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~r3_orders_2(k2_yellow_1(sK0),X1,sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.53/0.57  fof(f348,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK1) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl5_9),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f347])).
% 1.53/0.57  fof(f347,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK1) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl5_9),
% 1.53/0.57    inference(resolution,[],[f140,f66])).
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    ( ! [X1] : (~r3_orders_2(k2_yellow_1(sK0),X1,sK1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,sK1)) ) | ~spl5_9),
% 1.53/0.57    inference(avatar_component_clause,[],[f139])).
% 1.53/0.57  fof(f354,plain,(
% 1.53/0.57    spl5_48),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f353])).
% 1.53/0.57  fof(f353,plain,(
% 1.53/0.57    $false | spl5_48),
% 1.53/0.57    inference(resolution,[],[f341,f42])).
% 1.53/0.57  fof(f341,plain,(
% 1.53/0.57    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | spl5_48),
% 1.53/0.57    inference(avatar_component_clause,[],[f339])).
% 1.53/0.57  fof(f337,plain,(
% 1.53/0.57    spl5_19),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f336])).
% 1.53/0.57  fof(f336,plain,(
% 1.53/0.57    $false | spl5_19),
% 1.53/0.57    inference(resolution,[],[f215,f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.53/0.57  fof(f215,plain,(
% 1.53/0.57    ~v3_orders_2(k2_yellow_1(sK0)) | spl5_19),
% 1.53/0.57    inference(avatar_component_clause,[],[f213])).
% 1.53/0.57  fof(f329,plain,(
% 1.53/0.57    spl5_18),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f328])).
% 1.53/0.57  fof(f328,plain,(
% 1.53/0.57    $false | spl5_18),
% 1.53/0.57    inference(resolution,[],[f208,f41])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    v2_lattice3(k2_yellow_1(sK0))),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f208,plain,(
% 1.53/0.57    ~v2_lattice3(k2_yellow_1(sK0)) | spl5_18),
% 1.53/0.57    inference(avatar_component_clause,[],[f206])).
% 1.53/0.57  fof(f255,plain,(
% 1.53/0.57    ~spl5_3 | spl5_29),
% 1.53/0.57    inference(avatar_split_clause,[],[f159,f253,f97])).
% 1.53/0.57  fof(f159,plain,(
% 1.53/0.57    ( ! [X9] : (m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X9,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X9,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) )),
% 1.53/0.57    inference(resolution,[],[f43,f67])).
% 1.53/0.57  fof(f67,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.53/0.57    inference(flattening,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 1.53/0.57  fof(f204,plain,(
% 1.53/0.57    spl5_3),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f203])).
% 1.53/0.57  fof(f203,plain,(
% 1.53/0.57    $false | spl5_3),
% 1.53/0.57    inference(resolution,[],[f99,f50])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.53/0.57  fof(f99,plain,(
% 1.53/0.57    ~l1_orders_2(k2_yellow_1(sK0)) | spl5_3),
% 1.53/0.57    inference(avatar_component_clause,[],[f97])).
% 1.53/0.57  fof(f202,plain,(
% 1.53/0.57    spl5_2),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f201])).
% 1.53/0.57  fof(f201,plain,(
% 1.53/0.57    $false | spl5_2),
% 1.53/0.57    inference(resolution,[],[f95,f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f9])).
% 1.53/0.57  fof(f95,plain,(
% 1.53/0.57    ~v5_orders_2(k2_yellow_1(sK0)) | spl5_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f93])).
% 1.53/0.57  fof(f191,plain,(
% 1.53/0.57    spl5_7 | spl5_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f151,f189,f131])).
% 1.53/0.57  fof(f131,plain,(
% 1.53/0.57    spl5_7 <=> v1_xboole_0(sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.53/0.57  fof(f151,plain,(
% 1.53/0.57    ( ! [X1] : (r1_tarski(X1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) )),
% 1.53/0.57    inference(resolution,[],[f43,f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.53/0.57    inference(nnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.53/0.57  fof(f179,plain,(
% 1.53/0.57    ~spl5_7),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f178])).
% 1.53/0.57  fof(f178,plain,(
% 1.53/0.57    $false | ~spl5_7),
% 1.53/0.57    inference(resolution,[],[f133,f40])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ~v1_xboole_0(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f133,plain,(
% 1.53/0.57    v1_xboole_0(sK0) | ~spl5_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f131])).
% 1.53/0.57  fof(f177,plain,(
% 1.53/0.57    ~spl5_12 | ~spl5_13),
% 1.53/0.57    inference(avatar_split_clause,[],[f167,f174,f170])).
% 1.53/0.57  fof(f167,plain,(
% 1.53/0.57    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 1.53/0.57    inference(resolution,[],[f69,f70])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f68,f64])).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f28])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.57    inference(flattening,[],[f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.53/0.57  fof(f69,plain,(
% 1.53/0.57    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.53/0.57    inference(definition_unfolding,[],[f44,f64])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f141,plain,(
% 1.53/0.57    spl5_7 | spl5_9),
% 1.53/0.57    inference(avatar_split_clause,[],[f114,f139,f131])).
% 1.53/0.57  fof(f114,plain,(
% 1.53/0.57    ( ! [X1] : (r1_tarski(X1,sK1) | ~r3_orders_2(k2_yellow_1(sK0),X1,sK1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) )),
% 1.53/0.57    inference(resolution,[],[f42,f53])).
% 1.53/0.57  fof(f112,plain,(
% 1.53/0.57    ~spl5_3 | ~spl5_1),
% 1.53/0.57    inference(avatar_split_clause,[],[f87,f89,f97])).
% 1.53/0.57  fof(f87,plain,(
% 1.53/0.57    ~v2_struct_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0))),
% 1.53/0.57    inference(resolution,[],[f41,f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.53/0.57    inference(flattening,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (5920)------------------------------
% 1.53/0.57  % (5920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (5920)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (5920)Memory used [KB]: 6908
% 1.53/0.57  % (5920)Time elapsed: 0.137 s
% 1.53/0.57  % (5920)------------------------------
% 1.53/0.57  % (5920)------------------------------
% 1.53/0.57  % (5904)Success in time 0.194 s
%------------------------------------------------------------------------------
