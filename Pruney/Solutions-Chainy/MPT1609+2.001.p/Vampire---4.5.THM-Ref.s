%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 421 expanded)
%              Number of leaves         :   31 ( 144 expanded)
%              Depth                    :   18
%              Number of atoms          :  634 (1308 expanded)
%              Number of equality atoms :   64 ( 280 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f149,f225,f227,f232,f243,f245,f249,f253,f256,f260,f263])).

fof(f263,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(avatar_split_clause,[],[f262,f240,f222,f218])).

fof(f218,plain,
    ( spl8_12
  <=> m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f222,plain,
    ( spl8_13
  <=> m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f240,plain,
    ( spl8_15
  <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f262,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | spl8_15 ),
    inference(resolution,[],[f242,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f140,f55])).

fof(f55,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f84,f55])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(definition_unfolding,[],[f72,f67,f52,f52])).

fof(f52,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f67,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f242,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f260,plain,(
    spl8_14 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl8_14 ),
    inference(resolution,[],[f254,f142])).

fof(f142,plain,(
    ~ v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f139,f94])).

fof(f94,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f78,f55])).

fof(f78,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
            | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
          | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
        | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | ~ v1_xboole_0(k9_setfam_1(X1)) ) ),
    inference(condensation,[],[f138])).

fof(f138,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ m1_subset_1(X3,k9_setfam_1(X2))
      | ~ v1_xboole_0(k9_setfam_1(X2)) ) ),
    inference(resolution,[],[f136,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f135,f55])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f83,f55])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(definition_unfolding,[],[f73,f52,f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f254,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | spl8_14 ),
    inference(resolution,[],[f238,f198])).

fof(f198,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f186,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v2_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(X0))
      | ( ~ r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0)
        & r2_hidden(sK6(X0),X0)
        & r2_hidden(sK5(X0),X0) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k3_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0)
        & r2_hidden(sK6(X0),X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(X0))
      | ? [X1,X2] :
          ( ~ r2_hidden(k3_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(X0))
      | ? [X1,X2] :
          ( ~ r2_hidden(k3_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( ! [X1,X2] :
            ( ( r2_hidden(X2,X0)
              & r2_hidden(X1,X0) )
           => r2_hidden(k3_xboole_0(X1,X2),X0) )
       => v2_lattice3(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_1)).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v2_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0))
      | ~ r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f160,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f150,f69])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(k9_setfam_1(X0)),k9_setfam_1(X0))
      | ~ m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f141,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5(X0),sK6(X0))),X0)
      | v2_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f62,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(X0))
      | ~ r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f238,plain,
    ( ~ v2_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl8_14
  <=> v2_lattice3(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f256,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_11 ),
    inference(avatar_split_clause,[],[f255,f214,f222,f218])).

fof(f214,plain,
    ( spl8_11
  <=> r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f255,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | spl8_11 ),
    inference(resolution,[],[f216,f136])).

fof(f216,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f253,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl8_13 ),
    inference(resolution,[],[f224,f95])).

fof(f95,plain,(
    m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f77,f55])).

fof(f77,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f224,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f249,plain,(
    spl8_12 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl8_12 ),
    inference(resolution,[],[f220,f94])).

fof(f220,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f218])).

fof(f245,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl8_10 ),
    inference(resolution,[],[f212,f80])).

fof(f80,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f212,plain,
    ( ~ l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_10
  <=> l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f243,plain,
    ( ~ spl8_8
    | ~ spl8_14
    | ~ spl8_10
    | spl8_3
    | ~ spl8_15
    | ~ spl8_12
    | ~ spl8_13
    | spl8_2 ),
    inference(avatar_split_clause,[],[f234,f90,f222,f218,f240,f100,f210,f236,f202])).

fof(f202,plain,
    ( spl8_8
  <=> v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f100,plain,
    ( spl8_3
  <=> v1_xboole_0(k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f90,plain,
    ( spl8_2
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f234,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_2 ),
    inference(superposition,[],[f92,f192])).

fof(f192,plain,(
    ! [X4,X5,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,X3)
      | ~ m1_subset_1(X5,X3)
      | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(forward_demodulation,[],[f190,f55])).

fof(f190,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,X3)
      | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,X3)
      | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(forward_demodulation,[],[f187,f55])).

fof(f187,plain,(
    ! [X4,X5,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(superposition,[],[f184,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f183,f55])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f67,f67])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f92,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f232,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl8_9 ),
    inference(resolution,[],[f228,f142])).

fof(f228,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | spl8_9 ),
    inference(resolution,[],[f208,f182])).

fof(f182,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f180,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(X0))
      | ( ~ r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0)
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k2_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0)
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(X0))
      | ? [X1,X2] :
          ( ~ r2_hidden(k2_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(X0))
      | ? [X1,X2] :
          ( ~ r2_hidden(k2_xboole_0(X1,X2),X0)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( ! [X1,X2] :
            ( ( r2_hidden(X2,X0)
              & r2_hidden(X1,X0) )
           => r2_hidden(k2_xboole_0(X1,X2),X0) )
       => v1_lattice3(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow_1)).

fof(f180,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f165,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0))
      | ~ r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f157,f69])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0))
      | ~ r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f137,f69])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k9_setfam_1(X0)),k9_setfam_1(X0))
      | ~ m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f136,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0)
      | v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f208,plain,
    ( ~ v1_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_9
  <=> v1_lattice3(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f227,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl8_8 ),
    inference(resolution,[],[f204,f79])).

fof(f79,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f204,plain,
    ( ~ v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f225,plain,
    ( ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | spl8_3
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | spl8_1 ),
    inference(avatar_split_clause,[],[f200,f86,f222,f218,f214,f100,f210,f206,f202])).

fof(f86,plain,
    ( spl8_1
  <=> k2_xboole_0(sK1,sK2) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f200,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(k9_setfam_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))
    | spl8_1 ),
    inference(superposition,[],[f88,f174])).

fof(f174,plain,(
    ! [X4,X5,X3] :
      ( k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5)
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k2_xboole_0(X4,X5),X3)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,X3)
      | ~ m1_subset_1(X5,X3)
      | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k2_xboole_0(X4,X5),X3)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(forward_demodulation,[],[f172,f55])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,X3)
      | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k2_xboole_0(X4,X5),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,X3)
      | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5)
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k2_xboole_0(X4,X5),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(forward_demodulation,[],[f169,f55])).

fof(f169,plain,(
    ! [X4,X5,X3] :
      ( k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5)
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,X3)
      | ~ r2_hidden(k2_xboole_0(X4,X5),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v1_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3)) ) ),
    inference(superposition,[],[f162,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f161,f55])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f63,f55])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
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
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f88,plain,
    ( k2_xboole_0(sK1,sK2) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f149,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl8_3 ),
    inference(resolution,[],[f142,f101])).

fof(f101,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f93,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f76,f90,f86])).

fof(f76,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f51,f67,f52,f52])).

fof(f51,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (31267)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (31280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (31273)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (31274)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (31282)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (31271)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (31281)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (31279)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (31270)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (31272)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (31269)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (31276)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (31277)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (31265)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (31269)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f93,f149,f225,f227,f232,f243,f245,f249,f253,f256,f260,f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ~spl8_12 | ~spl8_13 | spl8_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f262,f240,f222,f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    spl8_12 <=> m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl8_13 <=> m1_subset_1(sK2,k9_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl8_15 <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | spl8_15),
% 0.21/0.50    inference(resolution,[],[f242,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f140,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f84,f55])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f72,f67,f52,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0)) | spl8_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f240])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl8_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    $false | spl8_14),
% 0.21/0.50    inference(resolution,[],[f254,f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f139,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f78,f55])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.21/0.50    inference(definition_unfolding,[],[f49,f52])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k9_setfam_1(X1)) | ~v1_xboole_0(k9_setfam_1(X1))) )),
% 0.21/0.50    inference(condensation,[],[f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(X2)) | ~m1_subset_1(X3,k9_setfam_1(X2)) | ~v1_xboole_0(k9_setfam_1(X2))) )),
% 0.21/0.50    inference(resolution,[],[f136,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f135,f55])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f83,f55])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f73,f52,f52])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    v1_xboole_0(k9_setfam_1(sK0)) | spl8_14),
% 0.21/0.50    inference(resolution,[],[f238,f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f186,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v2_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0] : (v2_lattice3(k2_yellow_1(X0)) | (~r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0) & r2_hidden(sK6(X0),X0) & r2_hidden(sK5(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (? [X1,X2] : (~r2_hidden(k3_xboole_0(X1,X2),X0) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0) & r2_hidden(sK6(X0),X0) & r2_hidden(sK5(X0),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (v2_lattice3(k2_yellow_1(X0)) | ? [X1,X2] : (~r2_hidden(k3_xboole_0(X1,X2),X0) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((v2_lattice3(k2_yellow_1(X0)) | ? [X1,X2] : (~r2_hidden(k3_xboole_0(X1,X2),X0) & (r2_hidden(X2,X0) & r2_hidden(X1,X0)))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => (! [X1,X2] : ((r2_hidden(X2,X0) & r2_hidden(X1,X0)) => r2_hidden(k3_xboole_0(X1,X2),X0)) => v2_lattice3(k2_yellow_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_1)).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f168,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v2_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0)) | ~r2_hidden(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f160,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK6(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f150,f69])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK6(k9_setfam_1(X0)),k9_setfam_1(X0)) | ~m1_subset_1(sK5(k9_setfam_1(X0)),k9_setfam_1(X0)) | v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f141,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_setfam_1(k2_tarski(sK5(X0),sK6(X0))),X0) | v2_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f62,f67])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (v2_lattice3(k2_yellow_1(X0)) | ~r2_hidden(k3_xboole_0(sK5(X0),sK6(X0)),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ~v2_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | spl8_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f236])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    spl8_14 <=> v2_lattice3(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~spl8_12 | ~spl8_13 | spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f255,f214,f222,f218])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    spl8_11 <=> r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | spl8_11),
% 0.21/0.50    inference(resolution,[],[f216,f136])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | spl8_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f214])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl8_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    $false | spl8_13),
% 0.21/0.50    inference(resolution,[],[f224,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    m1_subset_1(sK2,k9_setfam_1(sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f77,f55])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.21/0.50    inference(definition_unfolding,[],[f50,f52])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f222])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl8_12),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    $false | spl8_12),
% 0.21/0.50    inference(resolution,[],[f220,f94])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k9_setfam_1(sK0)) | spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f218])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl8_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    $false | spl8_10),
% 0.21/0.50    inference(resolution,[],[f212,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f54,f52])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : l1_orders_2(k3_yellow_1(X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl8_10 <=> l1_orders_2(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~spl8_8 | ~spl8_14 | ~spl8_10 | spl8_3 | ~spl8_15 | ~spl8_12 | ~spl8_13 | spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f234,f90,f222,f218,f240,f100,f210,f236,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl8_8 <=> v5_orders_2(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl8_3 <=> v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl8_2 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | ~v2_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | ~v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_2),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f233])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) | ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | ~v2_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | ~v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_2),
% 0.21/0.50    inference(superposition,[],[f92,f192])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3) | v1_xboole_0(X3) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X4,X3) | ~m1_subset_1(X5,X3) | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X4,X3) | ~r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3) | v1_xboole_0(X3) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f190,f55])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X5,X3) | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X4,X3) | ~r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X5,X3) | k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f187,f55])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k1_setfam_1(k2_tarski(X4,X5)),X3) | v1_xboole_0(X3) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.50    inference(superposition,[],[f184,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f183,f55])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f82,f55])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f64,f67,f67])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    spl8_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    $false | spl8_9),
% 0.21/0.51    inference(resolution,[],[f228,f142])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    v1_xboole_0(k9_setfam_1(sK0)) | spl8_9),
% 0.21/0.51    inference(resolution,[],[f208,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f180,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (v1_lattice3(k2_yellow_1(X0)) | (~r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (? [X1,X2] : (~r2_hidden(k2_xboole_0(X1,X2),X0) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (v1_lattice3(k2_yellow_1(X0)) | ? [X1,X2] : (~r2_hidden(k2_xboole_0(X1,X2),X0) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((v1_lattice3(k2_yellow_1(X0)) | ? [X1,X2] : (~r2_hidden(k2_xboole_0(X1,X2),X0) & (r2_hidden(X2,X0) & r2_hidden(X1,X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => (! [X1,X2] : ((r2_hidden(X2,X0) & r2_hidden(X1,X0)) => r2_hidden(k2_xboole_0(X1,X2),X0)) => v1_lattice3(k2_yellow_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow_1)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f165,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0)) | ~r2_hidden(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f157,f69])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0)) | ~r2_hidden(sK4(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f137,f69])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4(k9_setfam_1(X0)),k9_setfam_1(X0)) | ~m1_subset_1(sK3(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f136,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK3(X0),sK4(X0)),X0) | v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~v1_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl8_9 <=> v1_lattice3(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl8_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    $false | spl8_8),
% 0.21/0.51    inference(resolution,[],[f204,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f52])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : v5_orders_2(k3_yellow_1(X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f202])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~spl8_8 | ~spl8_9 | ~spl8_10 | spl8_3 | ~spl8_11 | ~spl8_12 | ~spl8_13 | spl8_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f200,f86,f222,f218,f214,f100,f210,f206,f202])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl8_1 <=> k2_xboole_0(sK1,sK2) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | ~v1_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | ~v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k9_setfam_1(sK0)) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | ~r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | ~v1_lattice3(k2_yellow_1(k9_setfam_1(sK0))) | ~v5_orders_2(k2_yellow_1(k9_setfam_1(sK0))) | spl8_1),
% 0.21/0.51    inference(superposition,[],[f88,f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k2_xboole_0(X4,X5),X3) | v1_xboole_0(X3) | ~l1_orders_2(k2_yellow_1(X3)) | ~v1_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X4,X3) | ~m1_subset_1(X5,X3) | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5) | ~m1_subset_1(X4,X3) | ~r2_hidden(k2_xboole_0(X4,X5),X3) | v1_xboole_0(X3) | ~l1_orders_2(k2_yellow_1(X3)) | ~v1_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f172,f55])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X5,X3) | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5) | ~m1_subset_1(X4,X3) | ~r2_hidden(k2_xboole_0(X4,X5),X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v1_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X5,X3) | k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k2_xboole_0(X4,X5),X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v1_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f169,f55])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k13_lattice3(k2_yellow_1(X3),X4,X5) = k2_xboole_0(X4,X5) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,X3) | ~r2_hidden(k2_xboole_0(X4,X5),X3) | v1_xboole_0(X3) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v1_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3))) )),
% 0.21/0.51    inference(superposition,[],[f162,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f161,f55])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f63,f55])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k2_xboole_0(sK1,sK2) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~spl8_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    $false | ~spl8_3),
% 0.21/0.51    inference(resolution,[],[f142,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    v1_xboole_0(k9_setfam_1(sK0)) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f76,f90,f86])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.21/0.51    inference(definition_unfolding,[],[f51,f67,f52,f52])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31269)------------------------------
% 0.21/0.51  % (31269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31269)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31269)Memory used [KB]: 6268
% 0.21/0.51  % (31269)Time elapsed: 0.049 s
% 0.21/0.51  % (31269)------------------------------
% 0.21/0.51  % (31269)------------------------------
% 0.21/0.51  % (31268)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (31264)Success in time 0.151 s
%------------------------------------------------------------------------------
