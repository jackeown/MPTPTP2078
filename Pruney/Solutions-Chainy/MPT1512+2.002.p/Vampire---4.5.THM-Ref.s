%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 (1082 expanded)
%              Number of leaves         :   13 ( 221 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 (5943 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f180,f217])).

fof(f217,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f39,f36,f125,f86,f199,f194,f196,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f196,plain,
    ( ~ r1_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f36,f39,f86,f190,f57])).

% (29755)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f86,f86,f183,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f183,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f92,f89,f36,f91,f39,f86,f86,f119,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f119,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_5
  <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f91,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f89,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f39,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(f38,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f194,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f39,f36,f86,f190,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f199,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f35,f195,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f195,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f36,f39,f86,f190,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f39,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

% (29775)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f125,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f86,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f180,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f38,f36,f37,f39,f140,f135,f152,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,k16_lattice3(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f152,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK4(sK0,k16_lattice3(sK0,sK2),sK1))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f89,f92,f91,f36,f39,f85,f135,f137,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f137,plain,
    ( ~ r1_lattices(sK0,k16_lattice3(sK0,sK2),sK4(sK0,k16_lattice3(sK0,sK2),sK1))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f36,f39,f85,f128,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f128,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f38,f36,f37,f39,f85,f115,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
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
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(f115,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_4
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f85,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f135,plain,
    ( m1_subset_1(sK4(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f39,f36,f85,f128,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f140,plain,
    ( r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),sK1),sK2)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f35,f136,f47])).

fof(f136,plain,
    ( r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),sK1),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f36,f39,f85,f128,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f120,plain,
    ( ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f34,f117,f113])).

fof(f34,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:41:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (29758)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (29759)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (29759)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (29761)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (29768)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (29784)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f218,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f120,f180,f217])).
% 0.22/0.58  fof(f217,plain,(
% 0.22/0.58    spl7_5),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f215])).
% 0.22/0.58  fof(f215,plain,(
% 0.22/0.58    $false | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f39,f36,f125,f86,f199,f194,f196,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.22/0.58  fof(f196,plain,(
% 0.22/0.58    ~r1_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f36,f39,f86,f190,f57])).
% 0.22/0.58  % (29755)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,sK5(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    ~r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f38,f39,f36,f37,f86,f86,f183,f70])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 0.22/0.58    inference(equality_resolution,[],[f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.22/0.58  fof(f183,plain,(
% 0.22/0.58    ~r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f92,f89,f36,f91,f39,f86,f86,f119,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl7_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f117])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    spl7_5 <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    v8_lattices(sK0)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f37,f36,f39,f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.58    inference(flattening,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    v6_lattices(sK0)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f37,f36,f39,f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    v9_lattices(sK0)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f37,f36,f39,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    v10_lattices(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 0.22/0.58    inference(negated_conjecture,[],[f11])).
% 0.22/0.58  fof(f11,conjecture,(
% 0.22/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    v4_lattice3(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f194,plain,(
% 0.22/0.58    m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f39,f36,f86,f190,f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r4_lattice3(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK2) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f35,f195,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.58  fof(f195,plain,(
% 0.22/0.58    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl7_5),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f36,f39,f86,f190,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    r1_tarski(sK1,sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f36,f39,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.22/0.58  % (29775)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.59  fof(f125,plain,(
% 0.22/0.59    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f86,f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | r4_lattice3(X0,k15_lattice3(X0,X1),X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ~v2_struct_0(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    l3_lattices(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f180,plain,(
% 0.22/0.59    spl7_4),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.59  fof(f178,plain,(
% 0.22/0.59    $false | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f36,f37,f39,f140,f135,f152,f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,X2) | r3_lattices(X0,k16_lattice3(X0,X2),X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.59  fof(f152,plain,(
% 0.22/0.59    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK4(sK0,k16_lattice3(sK0,sK2),sK1)) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f89,f92,f91,f36,f39,f85,f135,f137,f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f137,plain,(
% 0.22/0.59    ~r1_lattices(sK0,k16_lattice3(sK0,sK2),sK4(sK0,k16_lattice3(sK0,sK2),sK1)) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f36,f39,f85,f128,f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,X1,sK4(X0,X1,X2)) | r3_lattice3(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.22/0.59  fof(f128,plain,(
% 0.22/0.59    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f36,f37,f39,f85,f115,f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | r3_lattices(X0,X1,k16_lattice3(X0,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | spl7_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f113])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    spl7_4 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f36,f39,f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.22/0.59  fof(f135,plain,(
% 0.22/0.59    m1_subset_1(sK4(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f39,f36,f85,f128,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattice3(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f140,plain,(
% 0.22/0.59    r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),sK1),sK2) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f35,f136,f47])).
% 0.22/0.59  fof(f136,plain,(
% 0.22/0.59    r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),sK1),sK1) | spl7_4),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f36,f39,f85,f128,f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f120,plain,(
% 0.22/0.59    ~spl7_4 | ~spl7_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f34,f117,f113])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (29759)------------------------------
% 0.22/0.59  % (29759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (29759)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (29759)Memory used [KB]: 6396
% 0.22/0.59  % (29759)Time elapsed: 0.136 s
% 0.22/0.59  % (29759)------------------------------
% 0.22/0.59  % (29759)------------------------------
% 1.78/0.59  % (29754)Success in time 0.226 s
%------------------------------------------------------------------------------
