%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 223 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 ( 801 expanded)
%              Number of equality atoms :   42 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f178,f198,f466,f495,f523,f538,f595,f600,f615,f622])).

fof(f622,plain,(
    ~ spl5_47 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl5_47 ),
    inference(resolution,[],[f590,f49])).

fof(f49,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
    & r2_hidden(k1_xboole_0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
      & r2_hidden(k1_xboole_0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f590,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl5_47
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f615,plain,(
    spl5_48 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | spl5_48 ),
    inference(resolution,[],[f606,f88])).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f606,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)),k1_xboole_0)
    | spl5_48 ),
    inference(resolution,[],[f594,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f594,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl5_48
  <=> r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f600,plain,
    ( ~ spl5_5
    | spl5_30
    | ~ spl5_34
    | spl5_46 ),
    inference(avatar_split_clause,[],[f598,f585,f462,f441,f170])).

fof(f170,plain,
    ( spl5_5
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

% (2637)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f441,plain,
    ( spl5_30
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f462,plain,
    ( spl5_34
  <=> r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f585,plain,
    ( spl5_46
  <=> sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f598,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK1)
    | spl5_46 ),
    inference(resolution,[],[f587,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,k2_yellow_1(X0),X1)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r2_lattice3(k2_yellow_1(X1),X2,X0)
      | sP0(X0,k2_yellow_1(X1),X2)
      | k1_yellow_0(k2_yellow_1(X1),X2) = X0 ) ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(X1))
      | sP0(X0,k2_yellow_1(X1),X2)
      | ~ r2_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,X1)
      | k1_yellow_0(k2_yellow_1(X1),X2) = X0 ) ),
    inference(forward_demodulation,[],[f101,f58])).

fof(f58,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,k2_yellow_1(X1),X2)
      | ~ r2_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | k1_yellow_0(k2_yellow_1(X1),X2) = X0 ) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | sP0(X1,X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | sP0(X1,X0,X2)
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | sP0(X1,X0,X2)
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f24,f29])).

% (2650)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f587,plain,
    ( ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)
    | spl5_46 ),
    inference(avatar_component_clause,[],[f585])).

fof(f595,plain,
    ( ~ spl5_46
    | spl5_47
    | ~ spl5_48
    | ~ spl5_8
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f578,f445,f188,f592,f589,f585])).

fof(f188,plain,
    ( spl5_8
  <=> m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f445,plain,
    ( spl5_31
  <=> m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,sK1)
        | ~ r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0))
        | ~ r2_hidden(X0,sK1)
        | ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) )
    | ~ spl5_31 ),
    inference(resolution,[],[f447,f270])).

fof(f270,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2(X0,k2_yellow_1(X1),X2),X1)
      | ~ m1_subset_1(X0,X1)
      | ~ r1_tarski(X0,sK2(X0,k2_yellow_1(X1),X2))
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,k2_yellow_1(X1),X2) ) ),
    inference(resolution,[],[f123,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK2(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X1,X0,sK2(X0,X1,X2))
        & r2_lattice3(X1,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK2(X0,X1,X2))
        & r2_lattice3(X1,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f123,plain,(
    ! [X4,X2,X5,X3] :
      ( r1_orders_2(k2_yellow_1(X3),X2,X4)
      | ~ m1_subset_1(X4,X3)
      | ~ m1_subset_1(X2,X3)
      | ~ r1_tarski(X2,X4)
      | ~ r2_hidden(X5,X3) ) ),
    inference(resolution,[],[f121,f74])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f84,f58])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f63,f58])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f118,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X1))
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f106,f58])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f105,f58])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f80,f57])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f447,plain,
    ( m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f445])).

fof(f538,plain,(
    ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl5_32 ),
    inference(trivial_inequality_removal,[],[f535])).

fof(f535,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_32 ),
    inference(superposition,[],[f50,f455])).

fof(f455,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl5_32
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f50,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f523,plain,
    ( spl5_30
    | spl5_31
    | ~ spl5_8
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f496,f462,f188,f445,f441])).

fof(f496,plain,
    ( m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_34 ),
    inference(resolution,[],[f464,f400])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0)
        | m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),X0),sK1)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f399,f58])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0)
        | m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),X0),u1_struct_0(k2_yellow_1(sK1))) )
    | ~ spl5_8 ),
    inference(resolution,[],[f204,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f204,plain,
    ( ! [X4] :
        ( sP0(k1_xboole_0,k2_yellow_1(sK1),X4)
        | ~ r2_lattice3(k2_yellow_1(sK1),X4,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X4) )
    | ~ spl5_8 ),
    inference(resolution,[],[f189,f108])).

fof(f189,plain,
    ( m1_subset_1(k1_xboole_0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f464,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f462])).

fof(f495,plain,
    ( ~ spl5_3
    | ~ spl5_8
    | spl5_34 ),
    inference(avatar_split_clause,[],[f494,f462,f188,f142])).

fof(f142,plain,
    ( spl5_3
  <=> l1_orders_2(k2_yellow_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f494,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | spl5_34 ),
    inference(forward_demodulation,[],[f493,f58])).

fof(f493,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | spl5_34 ),
    inference(resolution,[],[f463,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f463,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f462])).

fof(f466,plain,
    ( ~ spl5_3
    | spl5_32
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f451,f441,f453,f142])).

fof(f451,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | ~ spl5_30 ),
    inference(superposition,[],[f64,f443])).

fof(f443,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f441])).

fof(f64,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f198,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f196,f49])).

fof(f196,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl5_8 ),
    inference(resolution,[],[f190,f76])).

fof(f190,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f178,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f172,f49])).

fof(f172,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f170])).

fof(f153,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f144,f57])).

fof(f144,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (2627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (2644)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (2635)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (2628)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2645)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (2631)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (2636)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2629)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (2626)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (2623)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (2623)Refutation not found, incomplete strategy% (2623)------------------------------
% 0.21/0.53  % (2623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2623)Memory used [KB]: 1663
% 0.21/0.53  % (2623)Time elapsed: 0.115 s
% 0.21/0.53  % (2623)------------------------------
% 0.21/0.53  % (2623)------------------------------
% 0.21/0.53  % (2640)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (2647)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (2624)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (2640)Refutation not found, incomplete strategy% (2640)------------------------------
% 0.21/0.53  % (2640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2640)Memory used [KB]: 10618
% 0.21/0.53  % (2640)Time elapsed: 0.117 s
% 0.21/0.53  % (2640)------------------------------
% 0.21/0.53  % (2640)------------------------------
% 0.21/0.53  % (2631)Refutation not found, incomplete strategy% (2631)------------------------------
% 0.21/0.53  % (2631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2631)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2631)Memory used [KB]: 10618
% 0.21/0.53  % (2631)Time elapsed: 0.127 s
% 0.21/0.53  % (2631)------------------------------
% 0.21/0.53  % (2631)------------------------------
% 0.21/0.53  % (2625)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (2635)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f153,f178,f198,f466,f495,f523,f538,f595,f600,f615,f622])).
% 0.21/0.53  fof(f622,plain,(
% 0.21/0.53    ~spl5_47),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f616])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    $false | ~spl5_47),
% 0.21/0.53    inference(resolution,[],[f590,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.53  fof(f590,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_47),
% 0.21/0.53    inference(avatar_component_clause,[],[f589])).
% 0.21/0.53  fof(f589,plain,(
% 0.21/0.53    spl5_47 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.21/0.53  fof(f615,plain,(
% 0.21/0.53    spl5_48),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f614])).
% 0.21/0.53  fof(f614,plain,(
% 0.21/0.53    $false | spl5_48),
% 0.21/0.53    inference(resolution,[],[f606,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f74,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(rectify,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    r2_hidden(sK4(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)),k1_xboole_0) | spl5_48),
% 0.21/0.53    inference(resolution,[],[f594,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f594,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)) | spl5_48),
% 0.21/0.53    inference(avatar_component_clause,[],[f592])).
% 0.21/0.53  fof(f592,plain,(
% 0.21/0.53    spl5_48 <=> r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.53  fof(f600,plain,(
% 0.21/0.53    ~spl5_5 | spl5_30 | ~spl5_34 | spl5_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f598,f585,f462,f441,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl5_5 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  % (2637)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    spl5_30 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.53  fof(f462,plain,(
% 0.21/0.53    spl5_34 <=> r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.53  fof(f585,plain,(
% 0.21/0.53    spl5_46 <=> sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.21/0.53  fof(f598,plain,(
% 0.21/0.53    ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK1) | spl5_46),
% 0.21/0.53    inference(resolution,[],[f587,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X2,k2_yellow_1(X0),X1) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(resolution,[],[f108,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r2_lattice3(k2_yellow_1(X1),X2,X0) | sP0(X0,k2_yellow_1(X1),X2) | k1_yellow_0(k2_yellow_1(X1),X2) = X0) )),
% 0.21/0.53    inference(resolution,[],[f102,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X1)) | sP0(X0,k2_yellow_1(X1),X2) | ~r2_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,X1) | k1_yellow_0(k2_yellow_1(X1),X2) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f101,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X0,k2_yellow_1(X1),X2) | ~r2_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | k1_yellow_0(k2_yellow_1(X1),X2) = X0) )),
% 0.21/0.53    inference(resolution,[],[f72,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | sP0(X1,X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | sP0(X1,X0,X2) | ~r2_lattice3(X0,X2,X1)) & ((! [X3] : (r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.53    inference(rectify,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | sP0(X1,X0,X2) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.53    inference(definition_folding,[],[f24,f29])).
% 0.21/0.53  % (2650)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.53    inference(rectify,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) | spl5_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f585])).
% 0.21/0.53  fof(f595,plain,(
% 0.21/0.53    ~spl5_46 | spl5_47 | ~spl5_48 | ~spl5_8 | ~spl5_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f578,f445,f188,f592,f589,f585])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    spl5_8 <=> m1_subset_1(k1_xboole_0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    spl5_31 <=> m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.53  fof(f578,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK1) | ~r1_tarski(k1_xboole_0,sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)) | ~r2_hidden(X0,sK1) | ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)) ) | ~spl5_31),
% 0.21/0.53    inference(resolution,[],[f447,f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2(X0,k2_yellow_1(X1),X2),X1) | ~m1_subset_1(X0,X1) | ~r1_tarski(X0,sK2(X0,k2_yellow_1(X1),X2)) | ~r2_hidden(X3,X1) | ~sP0(X0,k2_yellow_1(X1),X2)) )),
% 0.21/0.53    inference(resolution,[],[f123,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,sK2(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((~r1_orders_2(X1,X0,sK2(X0,X1,X2)) & r2_lattice3(X1,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~sP0(X0,X1,X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK2(X0,X1,X2)) & r2_lattice3(X1,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X4,X2,X5,X3] : (r1_orders_2(k2_yellow_1(X3),X2,X4) | ~m1_subset_1(X4,X3) | ~m1_subset_1(X2,X3) | ~r1_tarski(X2,X4) | ~r2_hidden(X5,X3)) )),
% 0.21/0.53    inference(resolution,[],[f121,f74])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f119,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f84,f58])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f63,f58])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f118,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X1)) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f107,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f58])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f105,f58])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f80,f57])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | ~spl5_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f445])).
% 0.21/0.53  fof(f538,plain,(
% 0.21/0.53    ~spl5_32),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f537])).
% 0.21/0.53  fof(f537,plain,(
% 0.21/0.53    $false | ~spl5_32),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f535])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~spl5_32),
% 0.21/0.53    inference(superposition,[],[f50,f455])).
% 0.21/0.53  fof(f455,plain,(
% 0.21/0.53    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) | ~spl5_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f453])).
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    spl5_32 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f523,plain,(
% 0.21/0.53    spl5_30 | spl5_31 | ~spl5_8 | ~spl5_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f496,f462,f188,f445,f441])).
% 0.21/0.53  fof(f496,plain,(
% 0.21/0.53    m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | (~spl5_8 | ~spl5_34)),
% 0.21/0.53    inference(resolution,[],[f464,f400])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) | m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),X0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0)) ) | ~spl5_8),
% 0.21/0.53    inference(forward_demodulation,[],[f399,f58])).
% 0.21/0.53  fof(f399,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0) | m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),X0),u1_struct_0(k2_yellow_1(sK1)))) ) | ~spl5_8),
% 0.21/0.53    inference(resolution,[],[f204,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ( ! [X4] : (sP0(k1_xboole_0,k2_yellow_1(sK1),X4) | ~r2_lattice3(k2_yellow_1(sK1),X4,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X4)) ) | ~spl5_8),
% 0.21/0.53    inference(resolution,[],[f189,f108])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    m1_subset_1(k1_xboole_0,sK1) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f188])).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | ~spl5_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f462])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    ~spl5_3 | ~spl5_8 | spl5_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f494,f462,f188,f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl5_3 <=> l1_orders_2(k2_yellow_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f494,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,sK1) | ~l1_orders_2(k2_yellow_1(sK1)) | spl5_34),
% 0.21/0.53    inference(forward_demodulation,[],[f493,f58])).
% 0.21/0.53  fof(f493,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | ~l1_orders_2(k2_yellow_1(sK1)) | spl5_34),
% 0.21/0.53    inference(resolution,[],[f463,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | spl5_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f462])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    ~spl5_3 | spl5_32 | ~spl5_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f451,f441,f453,f142])).
% 0.21/0.53  fof(f451,plain,(
% 0.21/0.53    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) | ~l1_orders_2(k2_yellow_1(sK1)) | ~spl5_30),
% 0.21/0.53    inference(superposition,[],[f64,f443])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | ~spl5_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f441])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    spl5_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    $false | spl5_8),
% 0.21/0.53    inference(resolution,[],[f196,f49])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ~r2_hidden(k1_xboole_0,sK1) | spl5_8),
% 0.21/0.53    inference(resolution,[],[f190,f76])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,sK1) | spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f188])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    $false | spl5_5),
% 0.21/0.53    inference(resolution,[],[f172,f49])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r2_hidden(k1_xboole_0,sK1) | spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    $false | spl5_3),
% 0.21/0.53    inference(resolution,[],[f144,f57])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ~l1_orders_2(k2_yellow_1(sK1)) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f142])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2635)------------------------------
% 0.21/0.53  % (2635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2635)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2635)Memory used [KB]: 6524
% 0.21/0.53  % (2635)Time elapsed: 0.114 s
% 0.21/0.53  % (2635)------------------------------
% 0.21/0.53  % (2635)------------------------------
% 0.21/0.53  % (2625)Refutation not found, incomplete strategy% (2625)------------------------------
% 0.21/0.53  % (2625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2625)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2625)Memory used [KB]: 10746
% 0.21/0.53  % (2625)Time elapsed: 0.126 s
% 0.21/0.53  % (2625)------------------------------
% 0.21/0.53  % (2625)------------------------------
% 0.21/0.53  % (2618)Success in time 0.174 s
%------------------------------------------------------------------------------
