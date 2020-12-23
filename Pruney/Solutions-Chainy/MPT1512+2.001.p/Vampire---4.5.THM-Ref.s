%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:45 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   87 (1014 expanded)
%              Number of leaves         :   12 ( 206 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 (5543 expanded)
%              Number of equality atoms :   10 (  32 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f170,f203])).

fof(f203,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f36,f133,f93,f187,f183,f185,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

% (20651)Termination reason: Refutation not found, incomplete strategy
fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f185,plain,
    ( ~ r1_lattices(sK0,sK7(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f36,f39,f93,f178,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f178,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f93,f93,f172,f75])).

% (20651)Memory used [KB]: 10746
fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

% (20651)Time elapsed: 0.143 s
fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (20651)------------------------------
% (20651)------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f172,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f99,f96,f36,f98,f39,f93,f93,f126,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f126,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_5
  <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f98,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f96,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f38,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f183,plain,
    ( m1_subset_1(sK7(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f36,f93,f178,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f187,plain,
    ( r2_hidden(sK7(sK0,k15_lattice3(sK0,sK2),sK1),sK2)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f35,f184,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f184,plain,
    ( r2_hidden(sK7(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f36,f39,f93,f178,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f39,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f133,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f93,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f170,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f39,f36,f132,f92,f152,f140,f142,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f142,plain,
    ( ~ r1_lattices(sK0,k16_lattice3(sK0,sK2),sK6(sK0,k16_lattice3(sK0,sK2),sK1))
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f36,f39,f92,f138,f61])).

% (20655)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,sK6(X0,X1,X2))
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f92,f92,f122,f73])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f122,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_4
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f140,plain,
    ( m1_subset_1(sK6(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f39,f36,f92,f138,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f152,plain,
    ( r2_hidden(sK6(sK0,k16_lattice3(sK0,sK2),sK1),sK2)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f35,f141,f55])).

fof(f141,plain,
    ( r2_hidden(sK6(sK0,k16_lattice3(sK0,sK2),sK1),sK1)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f36,f39,f92,f138,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f39,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f132,plain,(
    ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f92,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,
    ( ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f34,f124,f120])).

fof(f34,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:00:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (20637)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (20636)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (20652)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (20636)Refutation not found, incomplete strategy% (20636)------------------------------
% 0.20/0.52  % (20636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20643)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (20636)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  % (20646)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  
% 0.20/0.52  % (20636)Memory used [KB]: 10746
% 0.20/0.52  % (20636)Time elapsed: 0.111 s
% 0.20/0.52  % (20636)------------------------------
% 0.20/0.52  % (20636)------------------------------
% 0.20/0.53  % (20634)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (20641)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (20653)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (20635)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20648)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (20644)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (20644)Refutation not found, incomplete strategy% (20644)------------------------------
% 0.20/0.53  % (20644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20644)Memory used [KB]: 10618
% 0.20/0.53  % (20644)Time elapsed: 0.130 s
% 0.20/0.53  % (20644)------------------------------
% 0.20/0.53  % (20644)------------------------------
% 0.20/0.53  % (20651)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (20638)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (20658)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (20650)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (20639)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (20656)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (20656)Refutation not found, incomplete strategy% (20656)------------------------------
% 0.20/0.55  % (20656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (20654)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (20642)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.56  % (20651)Refutation not found, incomplete strategy% (20651)------------------------------
% 1.45/0.56  % (20651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (20638)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f204,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(avatar_sat_refutation,[],[f127,f170,f203])).
% 1.45/0.56  fof(f203,plain,(
% 1.45/0.56    spl8_5),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f201])).
% 1.45/0.56  fof(f201,plain,(
% 1.45/0.56    $false | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f39,f36,f133,f93,f187,f183,f185,f62])).
% 1.45/0.56  fof(f62,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  % (20651)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f30])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f5])).
% 1.45/0.56  
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.45/0.56  fof(f185,plain,(
% 1.45/0.56    ~r1_lattices(sK0,sK7(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f93,f178,f65])).
% 1.45/0.56  fof(f65,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,sK7(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  fof(f178,plain,(
% 1.45/0.56    ~r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f93,f93,f172,f75])).
% 1.45/0.56  % (20651)Memory used [KB]: 10746
% 1.45/0.56  fof(f75,plain,(
% 1.45/0.56    ( ! [X0,X3,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 1.45/0.56    inference(equality_resolution,[],[f53])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 1.45/0.56    inference(cnf_transformation,[],[f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f25])).
% 1.45/0.56  % (20651)Time elapsed: 0.143 s
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f6])).
% 1.45/0.56  % (20651)------------------------------
% 1.45/0.56  % (20651)------------------------------
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 1.45/0.56  fof(f172,plain,(
% 1.45/0.56    ~r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f99,f96,f36,f98,f39,f93,f93,f126,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f22])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f21])).
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.45/0.56  fof(f126,plain,(
% 1.45/0.56    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl8_5),
% 1.45/0.56    inference(avatar_component_clause,[],[f124])).
% 1.45/0.56  fof(f124,plain,(
% 1.45/0.56    spl8_5 <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.45/0.56  fof(f98,plain,(
% 1.45/0.56    v8_lattices(sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f37,f36,f39,f70])).
% 1.45/0.56  fof(f70,plain,(
% 1.45/0.56    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.45/0.56    inference(flattening,[],[f32])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.45/0.56  fof(f96,plain,(
% 1.45/0.56    v6_lattices(sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f37,f36,f39,f68])).
% 1.45/0.56  fof(f68,plain,(
% 1.45/0.56    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f33])).
% 1.45/0.56  fof(f99,plain,(
% 1.45/0.56    v9_lattices(sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f37,f36,f39,f71])).
% 1.45/0.56  fof(f71,plain,(
% 1.45/0.56    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f33])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    v10_lattices(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,plain,(
% 1.45/0.56    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f13])).
% 1.45/0.56  fof(f13,plain,(
% 1.45/0.56    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,negated_conjecture,(
% 1.45/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.45/0.56    inference(negated_conjecture,[],[f11])).
% 1.45/0.56  fof(f11,conjecture,(
% 1.45/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    v4_lattice3(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  fof(f183,plain,(
% 1.45/0.56    m1_subset_1(sK7(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f39,f36,f93,f178,f63])).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r4_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  fof(f187,plain,(
% 1.45/0.56    r2_hidden(sK7(sK0,k15_lattice3(sK0,sK2),sK1),sK2) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f35,f184,f55])).
% 1.45/0.56  fof(f55,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.56  fof(f184,plain,(
% 1.45/0.56    r2_hidden(sK7(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl8_5),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f93,f178,f64])).
% 1.45/0.56  fof(f64,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK7(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    r1_tarski(sK1,sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  fof(f93,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f49])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f23])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.45/0.56  fof(f133,plain,(
% 1.45/0.56    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f93,f74])).
% 1.45/0.56  fof(f74,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | r4_lattice3(X0,k15_lattice3(X0,X1),X1)) )),
% 1.45/0.56    inference(equality_resolution,[],[f54])).
% 1.45/0.56  fof(f54,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2) )),
% 1.45/0.56    inference(cnf_transformation,[],[f26])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ~v2_struct_0(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    l3_lattices(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  fof(f170,plain,(
% 1.45/0.56    spl8_4),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f168])).
% 1.45/0.56  fof(f168,plain,(
% 1.45/0.56    $false | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f39,f36,f132,f92,f152,f140,f142,f58])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.45/0.56  fof(f142,plain,(
% 1.45/0.56    ~r1_lattices(sK0,k16_lattice3(sK0,sK2),sK6(sK0,k16_lattice3(sK0,sK2),sK1)) | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f92,f138,f61])).
% 1.45/0.56  % (20655)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  fof(f61,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,X1,sK6(X0,X1,X2)) | r3_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f138,plain,(
% 1.45/0.56    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f92,f92,f122,f73])).
% 1.45/0.56  fof(f73,plain,(
% 1.45/0.56    ( ! [X2,X0,X3] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 1.45/0.56    inference(equality_resolution,[],[f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 1.45/0.56  fof(f122,plain,(
% 1.45/0.56    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | spl8_4),
% 1.45/0.56    inference(avatar_component_clause,[],[f120])).
% 1.45/0.56  fof(f120,plain,(
% 1.45/0.56    spl8_4 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.45/0.56  fof(f140,plain,(
% 1.45/0.56    m1_subset_1(sK6(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f39,f36,f92,f138,f59])).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f152,plain,(
% 1.45/0.56    r2_hidden(sK6(sK0,k16_lattice3(sK0,sK2),sK1),sK2) | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f35,f141,f55])).
% 1.45/0.56  fof(f141,plain,(
% 1.45/0.56    r2_hidden(sK6(sK0,k16_lattice3(sK0,sK2),sK1),sK1) | spl8_4),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f92,f138,f60])).
% 1.45/0.56  fof(f60,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f92,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f36,f39,f40])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,plain,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f15])).
% 1.45/0.56  fof(f15,plain,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 1.45/0.56  fof(f132,plain,(
% 1.45/0.56    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f92,f72])).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ( ! [X2,X0] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | r3_lattice3(X0,k16_lattice3(X0,X2),X2)) )),
% 1.45/0.56    inference(equality_resolution,[],[f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f127,plain,(
% 1.45/0.56    ~spl8_4 | ~spl8_5),
% 1.45/0.56    inference(avatar_split_clause,[],[f34,f124,f120])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 1.45/0.56    inference(cnf_transformation,[],[f14])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (20638)------------------------------
% 1.45/0.56  % (20638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (20638)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (20638)Memory used [KB]: 6396
% 1.45/0.56  % (20638)Time elapsed: 0.150 s
% 1.45/0.56  % (20638)------------------------------
% 1.45/0.56  % (20638)------------------------------
% 1.45/0.56  % (20662)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.56  % (20661)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.56  % (20656)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (20656)Memory used [KB]: 10746
% 1.45/0.56  % (20656)Time elapsed: 0.138 s
% 1.45/0.56  % (20656)------------------------------
% 1.45/0.56  % (20656)------------------------------
% 1.45/0.56  % (20657)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (20660)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (20659)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.57  % (20649)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.57  % (20633)Success in time 0.206 s
%------------------------------------------------------------------------------
