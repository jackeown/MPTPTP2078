%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  131 (2540 expanded)
%              Number of leaves         :   16 ( 533 expanded)
%              Depth                    :   21
%              Number of atoms          :  522 (10802 expanded)
%              Number of equality atoms :   17 (1390 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16571)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (16580)Refutation not found, incomplete strategy% (16580)------------------------------
% (16580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16580)Termination reason: Refutation not found, incomplete strategy

% (16580)Memory used [KB]: 10746
% (16580)Time elapsed: 0.202 s
% (16580)------------------------------
% (16580)------------------------------
% (16571)Refutation not found, incomplete strategy% (16571)------------------------------
% (16571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16571)Termination reason: Refutation not found, incomplete strategy

% (16571)Memory used [KB]: 10746
% (16571)Time elapsed: 0.209 s
% (16571)------------------------------
% (16571)------------------------------
% (16574)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f116,f127,f131,f135,f143,f157,f161,f176,f182,f320])).

fof(f320,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f206,f207,f243,f242,f239,f85])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_lattice3(sK1,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,X4)
      | r1_orders_2(sK1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f80,f71])).

fof(f71,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f18,f37,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f37,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f17,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f17,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( ( v3_lattice3(X0)
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
             => v3_lattice3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( ( v3_lattice3(X0)
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
           => v3_lattice3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_0)).

fof(f18,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(X3,X4)
      | r1_orders_2(sK1,X3,X2)
      | ~ r2_lattice3(sK1,X4,X2) ) ),
    inference(backward_demodulation,[],[f41,f71])).

fof(f41,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(X3,X4)
      | r1_orders_2(sK1,X3,X2)
      | ~ r2_lattice3(sK1,X4,X2) ) ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
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

fof(f239,plain,
    ( ~ r1_orders_2(sK1,sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),sK4(sK1,sK3(sK0,sK2(sK1))))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f206,f233,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f233,plain,
    ( ~ r2_lattice3(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1))))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f21,f19,f206,f228,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_lattice3(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,sK3(X0,X1),X3)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).

fof(f228,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1))))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f21,f47,f206,f219,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f219,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1)))),u1_orders_2(sK0))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f47,f206,f208,f86])).

fof(f86,plain,(
    ! [X10,X9] :
      ( r1_orders_2(sK1,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f83,f71])).

fof(f83,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK1))
      | r1_orders_2(sK1,X9,X10) ) ),
    inference(backward_demodulation,[],[f75,f71])).

fof(f75,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | r1_orders_2(sK1,X9,X10) ) ),
    inference(backward_demodulation,[],[f44,f72])).

fof(f72,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(unit_resulting_resolution,[],[f18,f37,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK1))
      | r1_orders_2(sK1,X9,X10) ) ),
    inference(resolution,[],[f17,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f208,plain,
    ( ~ r1_orders_2(sK1,sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1))))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f47,f203,f115])).

fof(f115,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2(sK1),X1)
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_5
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X1))
        | ~ r2_lattice3(sK1,sK2(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f203,plain,
    ( ! [X0] : r2_lattice3(sK1,X0,sK3(sK0,X0))
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f47,f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,sK3(sK0,X0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK3(sK0,X0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,sK3(sK0,X0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(resolution,[],[f200,f81])).

fof(f81,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(sK1,X6,X5),X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_lattice3(sK1,X6,X5) ) ),
    inference(backward_demodulation,[],[f42,f71])).

fof(f42,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | r2_hidden(sK5(sK1,X6,X5),X6)
      | r2_lattice3(sK1,X6,X5) ) ),
    inference(resolution,[],[f17,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3(sK0,X1)),X1)
        | r2_lattice3(sK1,X0,sK3(sK0,X1))
        | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,sK3(sK0,X1))
        | ~ r2_hidden(sK5(sK1,X0,sK3(sK0,X1)),X1)
        | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,sK3(sK0,X1))
        | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(resolution,[],[f189,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f189,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(sK1,X3,sK3(sK0,X2)),u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,sK3(sK0,X2))
        | ~ r2_hidden(sK5(sK1,X3,sK3(sK0,X2)),X2)
        | ~ m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,sK3(sK0,X2))
        | ~ r2_hidden(sK5(sK1,X3,sK3(sK0,X2)),X2)
        | ~ m1_subset_1(sK5(sK1,X3,sK3(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(resolution,[],[f184,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK0,X0,sK3(sK0,X1))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X0] : r2_lattice3(sK0,X0,sK3(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f19,f21,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_lattice3(sK0,X4,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,X4)
      | r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f21,f31])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK1,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK1,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(resolution,[],[f181,f126])).

fof(f181,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK1,X3,X2),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,X2) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_12
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK1,X3,X2),X2)
        | ~ m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f21,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f242,plain,
    ( m1_subset_1(sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),u1_struct_0(sK0))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f21,f206,f233,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f243,plain,
    ( r2_hidden(sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),sK2(sK1))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f21,f206,f233,f33])).

fof(f207,plain,
    ( r2_lattice3(sK1,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1))))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f47,f203,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,sK2(sK1),X0)
        | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0))
        | ~ r2_lattice3(sK1,sK2(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f206,plain,
    ( m1_subset_1(sK4(sK1,sK3(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f47,f203,f156])).

fof(f156,plain,
    ( ! [X2] :
        ( m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,sK2(sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_9
  <=> ! [X2] :
        ( m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,sK2(sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f182,plain,
    ( ~ spl6_1
    | spl6_12
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f171,f125,f180,f59])).

fof(f59,plain,
    ( spl6_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f171,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,X2)
        | ~ m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK5(sK1,X3,X2),X2) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,X2)
        | ~ m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK5(sK1,X3,X2),X2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f168,f36])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK1,X0,X1),X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK1,X0,X1),X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,X1)
        | r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f148,f126])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK1,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),u1_orders_2(sK0))
      | ~ m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK1,X1,X0) ) ),
    inference(resolution,[],[f86,f82])).

fof(f82,plain,(
    ! [X8,X7] :
      ( ~ r1_orders_2(sK1,sK5(sK1,X8,X7),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_lattice3(sK1,X8,X7) ) ),
    inference(backward_demodulation,[],[f43,f71])).

fof(f43,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK5(sK1,X8,X7),X7)
      | r2_lattice3(sK1,X8,X7) ) ),
    inference(resolution,[],[f17,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f176,plain,
    ( ~ spl6_1
    | spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f166,f159,f174,f59])).

fof(f159,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f164,f32])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f160,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(sK0,X1,X0),X0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
      | r2_lattice3(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(sK5(sK0,X1,X0),X0),u1_orders_2(sK0))
      | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,X1,X0) ) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X8,X7] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X8,X7),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_lattice3(sK0,X8,X7) ) ),
    inference(resolution,[],[f21,f34])).

fof(f56,plain,(
    ! [X10,X9] :
      ( r1_orders_2(sK0,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f21,f35])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( ~ spl6_6
    | spl6_10 ),
    inference(avatar_split_clause,[],[f98,f159,f121])).

fof(f121,plain,
    ( spl6_6
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ l1_orders_2(sK1)
      | ~ r1_orders_2(sK1,X0,X1) ) ),
    inference(forward_demodulation,[],[f97,f71])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | ~ r1_orders_2(sK1,X0,X1) ) ),
    inference(forward_demodulation,[],[f96,f71])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | ~ r1_orders_2(sK1,X0,X1) ) ),
    inference(superposition,[],[f36,f72])).

fof(f157,plain,
    ( spl6_4
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f94,f155,f121,f110])).

fof(f110,plain,
    ( spl6_4
  <=> v3_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f94,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_lattice3(sK1,sK2(sK1),X2)
      | ~ l1_orders_2(sK1)
      | v3_lattice3(sK1) ) ),
    inference(superposition,[],[f22,f71])).

fof(f22,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f143,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f20,f112])).

fof(f112,plain,
    ( v3_lattice3(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f20,plain,(
    ~ v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f135,plain,
    ( spl6_4
    | spl6_8 ),
    inference(avatar_split_clause,[],[f78,f133,f110])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK1,sK2(sK1),X0)
      | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0))
      | v3_lattice3(sK1) ) ),
    inference(backward_demodulation,[],[f38,f71])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_lattice3(sK1,sK2(sK1),X0)
      | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0))
      | v3_lattice3(sK1) ) ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | r2_lattice3(X0,sK2(X0),sK4(X0,X2))
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f17,f123])).

fof(f123,plain,
    ( ~ l1_orders_2(sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f127,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f93,f125,f121])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | r2_lattice3(sK1,X0,X1) ) ),
    inference(superposition,[],[f32,f71])).

fof(f116,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f79,f114,f110])).

fof(f79,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK1,sK2(sK1),X1)
      | ~ r1_orders_2(sK1,X1,sK4(sK1,X1))
      | v3_lattice3(sK1) ) ),
    inference(backward_demodulation,[],[f39,f71])).

fof(f39,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_lattice3(sK1,sK2(sK1),X1)
      | ~ r1_orders_2(sK1,X1,sK4(sK1,X1))
      | v3_lattice3(sK1) ) ),
    inference(resolution,[],[f17,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X2))
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f21,f61])).

fof(f61,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:58:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (16567)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (16556)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.56  % (16556)Refutation not found, incomplete strategy% (16556)------------------------------
% 1.45/0.56  % (16556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (16559)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.56  % (16556)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (16556)Memory used [KB]: 10746
% 1.58/0.56  % (16556)Time elapsed: 0.136 s
% 1.58/0.56  % (16556)------------------------------
% 1.58/0.56  % (16556)------------------------------
% 1.58/0.57  % (16576)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.57  % (16557)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.57  % (16582)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.57  % (16569)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.57  % (16560)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.57  % (16564)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.58  % (16576)Refutation not found, incomplete strategy% (16576)------------------------------
% 1.58/0.58  % (16576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (16566)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.58  % (16576)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (16576)Memory used [KB]: 10746
% 1.58/0.58  % (16576)Time elapsed: 0.159 s
% 1.58/0.58  % (16576)------------------------------
% 1.58/0.58  % (16576)------------------------------
% 1.58/0.58  % (16564)Refutation not found, incomplete strategy% (16564)------------------------------
% 1.58/0.58  % (16564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (16564)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (16564)Memory used [KB]: 10746
% 1.58/0.58  % (16564)Time elapsed: 0.162 s
% 1.58/0.58  % (16564)------------------------------
% 1.58/0.58  % (16564)------------------------------
% 1.58/0.58  % (16554)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.59  % (16577)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.59  % (16555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.59  % (16558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.58/0.59  % (16583)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.60  % (16578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.60  % (16561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.60  % (16570)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.61  % (16572)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.61  % (16575)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.61  % (16562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.61  % (16581)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.61  % (16563)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.61  % (16579)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.62  % (16568)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.62  % (16565)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.62  % (16573)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.63  % (16580)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.63  % (16558)Refutation found. Thanks to Tanya!
% 1.58/0.63  % SZS status Theorem for theBenchmark
% 1.58/0.63  % SZS output start Proof for theBenchmark
% 1.58/0.63  % (16571)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.63  % (16580)Refutation not found, incomplete strategy% (16580)------------------------------
% 1.58/0.63  % (16580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (16580)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.63  
% 1.58/0.63  % (16580)Memory used [KB]: 10746
% 1.58/0.63  % (16580)Time elapsed: 0.202 s
% 1.58/0.63  % (16580)------------------------------
% 1.58/0.63  % (16580)------------------------------
% 1.58/0.63  % (16571)Refutation not found, incomplete strategy% (16571)------------------------------
% 1.58/0.63  % (16571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (16571)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.63  
% 1.58/0.63  % (16571)Memory used [KB]: 10746
% 1.58/0.63  % (16571)Time elapsed: 0.209 s
% 1.58/0.63  % (16571)------------------------------
% 1.58/0.63  % (16571)------------------------------
% 1.58/0.64  % (16574)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.14/0.64  fof(f321,plain,(
% 2.14/0.64    $false),
% 2.14/0.64    inference(avatar_sat_refutation,[],[f69,f116,f127,f131,f135,f143,f157,f161,f176,f182,f320])).
% 2.14/0.64  fof(f320,plain,(
% 2.14/0.64    ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_12),
% 2.14/0.64    inference(avatar_contradiction_clause,[],[f316])).
% 2.14/0.64  fof(f316,plain,(
% 2.14/0.64    $false | (~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f206,f207,f243,f242,f239,f85])).
% 2.14/0.64  fof(f85,plain,(
% 2.14/0.64    ( ! [X4,X2,X3] : (~r2_lattice3(sK1,X4,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,X4) | r1_orders_2(sK1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f80,f71])).
% 2.14/0.64  fof(f71,plain,(
% 2.14/0.64    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f18,f37,f28])).
% 2.14/0.64  fof(f28,plain,(
% 2.14/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 2.14/0.64    inference(cnf_transformation,[],[f12])).
% 2.14/0.64  fof(f12,plain,(
% 2.14/0.64    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.14/0.64    inference(ennf_transformation,[],[f3])).
% 2.14/0.64  fof(f3,axiom,(
% 2.14/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 2.14/0.64  fof(f37,plain,(
% 2.14/0.64    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f17,f30])).
% 2.14/0.64  fof(f30,plain,(
% 2.14/0.64    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f13])).
% 2.14/0.64  fof(f13,plain,(
% 2.14/0.64    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(ennf_transformation,[],[f2])).
% 2.14/0.64  fof(f2,axiom,(
% 2.14/0.64    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 2.14/0.64  fof(f17,plain,(
% 2.14/0.64    l1_orders_2(sK1)),
% 2.14/0.64    inference(cnf_transformation,[],[f9])).
% 2.14/0.64  fof(f9,plain,(
% 2.14/0.64    ? [X0] : (? [X1] : (~v3_lattice3(X1) & v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 2.14/0.64    inference(flattening,[],[f8])).
% 2.14/0.64  fof(f8,plain,(
% 2.14/0.64    ? [X0] : (? [X1] : ((~v3_lattice3(X1) & (v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 2.14/0.64    inference(ennf_transformation,[],[f7])).
% 2.14/0.64  fof(f7,negated_conjecture,(
% 2.14/0.64    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ((v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) => v3_lattice3(X1))))),
% 2.14/0.64    inference(negated_conjecture,[],[f6])).
% 2.14/0.64  fof(f6,conjecture,(
% 2.14/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ((v3_lattice3(X0) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) => v3_lattice3(X1))))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_0)).
% 2.14/0.64  fof(f18,plain,(
% 2.14/0.64    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))),
% 2.14/0.64    inference(cnf_transformation,[],[f9])).
% 2.14/0.64  fof(f80,plain,(
% 2.14/0.64    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,X4) | r1_orders_2(sK1,X3,X2) | ~r2_lattice3(sK1,X4,X2)) )),
% 2.14/0.64    inference(backward_demodulation,[],[f41,f71])).
% 2.14/0.64  fof(f41,plain,(
% 2.14/0.64    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,X4) | r1_orders_2(sK1,X3,X2) | ~r2_lattice3(sK1,X4,X2)) )),
% 2.14/0.64    inference(resolution,[],[f17,f31])).
% 2.14/0.64  fof(f31,plain,(
% 2.14/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f15])).
% 2.14/0.64  fof(f15,plain,(
% 2.14/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(flattening,[],[f14])).
% 2.14/0.64  fof(f14,plain,(
% 2.14/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(ennf_transformation,[],[f5])).
% 2.14/0.64  fof(f5,axiom,(
% 2.14/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 2.14/0.64  fof(f239,plain,(
% 2.14/0.64    ~r1_orders_2(sK1,sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),sK4(sK1,sK3(sK0,sK2(sK1)))) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_11 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f206,f233,f175])).
% 2.14/0.64  fof(f175,plain,(
% 2.14/0.64    ( ! [X0,X1] : (~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_11),
% 2.14/0.64    inference(avatar_component_clause,[],[f174])).
% 2.14/0.64  fof(f174,plain,(
% 2.14/0.64    spl6_11 <=> ! [X1,X0] : (~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.14/0.64  fof(f233,plain,(
% 2.14/0.64    ~r2_lattice3(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f21,f19,f206,f228,f25])).
% 2.14/0.64  fof(f25,plain,(
% 2.14/0.64    ( ! [X0,X3,X1] : (~v3_lattice3(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,sK3(X0,X1),X3) | ~l1_orders_2(X0)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f11])).
% 2.14/0.64  fof(f11,plain,(
% 2.14/0.64    ! [X0] : ((v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(flattening,[],[f10])).
% 2.14/0.64  fof(f10,plain,(
% 2.14/0.64    ! [X0] : ((v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(ennf_transformation,[],[f4])).
% 2.14/0.64  fof(f4,axiom,(
% 2.14/0.64    ! [X0] : (l1_orders_2(X0) => (v3_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).
% 2.14/0.64  fof(f228,plain,(
% 2.14/0.64    ~r1_orders_2(sK0,sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1)))) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f21,f47,f206,f219,f36])).
% 2.14/0.64  fof(f36,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f16])).
% 2.14/0.64  fof(f16,plain,(
% 2.14/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.14/0.64    inference(ennf_transformation,[],[f1])).
% 2.14/0.64  fof(f1,axiom,(
% 2.14/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 2.14/0.64  fof(f219,plain,(
% 2.14/0.64    ~r2_hidden(k4_tarski(sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1)))),u1_orders_2(sK0)) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f47,f206,f208,f86])).
% 2.14/0.64  fof(f86,plain,(
% 2.14/0.64    ( ! [X10,X9] : (r1_orders_2(sK1,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f83,f71])).
% 2.14/0.64  fof(f83,plain,(
% 2.14/0.64    ( ! [X10,X9] : (~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK1)) | r1_orders_2(sK1,X9,X10)) )),
% 2.14/0.64    inference(backward_demodulation,[],[f75,f71])).
% 2.14/0.64  fof(f75,plain,(
% 2.14/0.64    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK1)) | ~m1_subset_1(X10,u1_struct_0(sK1)) | r1_orders_2(sK1,X9,X10)) )),
% 2.14/0.64    inference(backward_demodulation,[],[f44,f72])).
% 2.14/0.64  fof(f72,plain,(
% 2.14/0.64    u1_orders_2(sK0) = u1_orders_2(sK1)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f18,f37,f29])).
% 2.14/0.64  fof(f29,plain,(
% 2.14/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 2.14/0.64    inference(cnf_transformation,[],[f12])).
% 2.14/0.64  fof(f44,plain,(
% 2.14/0.64    ( ! [X10,X9] : (~m1_subset_1(X9,u1_struct_0(sK1)) | ~m1_subset_1(X10,u1_struct_0(sK1)) | ~r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK1)) | r1_orders_2(sK1,X9,X10)) )),
% 2.14/0.64    inference(resolution,[],[f17,f35])).
% 2.14/0.64  fof(f35,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f16])).
% 2.14/0.64  fof(f208,plain,(
% 2.14/0.64    ~r1_orders_2(sK1,sK3(sK0,sK2(sK1)),sK4(sK1,sK3(sK0,sK2(sK1)))) | (~spl6_5 | ~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f47,f203,f115])).
% 2.14/0.64  fof(f115,plain,(
% 2.14/0.64    ( ! [X1] : (~r2_lattice3(sK1,sK2(sK1),X1) | ~r1_orders_2(sK1,X1,sK4(sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_5),
% 2.14/0.64    inference(avatar_component_clause,[],[f114])).
% 2.14/0.64  fof(f114,plain,(
% 2.14/0.64    spl6_5 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK1,X1,sK4(sK1,X1)) | ~r2_lattice3(sK1,sK2(sK1),X1))),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.14/0.64  fof(f203,plain,(
% 2.14/0.64    ( ! [X0] : (r2_lattice3(sK1,X0,sK3(sK0,X0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f47,f202])).
% 2.14/0.64  fof(f202,plain,(
% 2.14/0.64    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,sK3(sK0,X0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(duplicate_literal_removal,[],[f201])).
% 2.14/0.64  fof(f201,plain,(
% 2.14/0.64    ( ! [X0] : (r2_lattice3(sK1,X0,sK3(sK0,X0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,sK3(sK0,X0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(resolution,[],[f200,f81])).
% 2.14/0.64  fof(f81,plain,(
% 2.14/0.64    ( ! [X6,X5] : (r2_hidden(sK5(sK1,X6,X5),X6) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_lattice3(sK1,X6,X5)) )),
% 2.14/0.64    inference(backward_demodulation,[],[f42,f71])).
% 2.14/0.64  fof(f42,plain,(
% 2.14/0.64    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | r2_hidden(sK5(sK1,X6,X5),X6) | r2_lattice3(sK1,X6,X5)) )),
% 2.14/0.64    inference(resolution,[],[f17,f33])).
% 2.14/0.64  fof(f33,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f15])).
% 2.14/0.64  fof(f200,plain,(
% 2.14/0.64    ( ! [X0,X1] : (~r2_hidden(sK5(sK1,X0,sK3(sK0,X1)),X1) | r2_lattice3(sK1,X0,sK3(sK0,X1)) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(duplicate_literal_removal,[],[f199])).
% 2.14/0.64  fof(f199,plain,(
% 2.14/0.64    ( ! [X0,X1] : (r2_lattice3(sK1,X0,sK3(sK0,X1)) | ~r2_hidden(sK5(sK1,X0,sK3(sK0,X1)),X1) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,sK3(sK0,X1)) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.64    inference(resolution,[],[f189,f126])).
% 2.14/0.65  fof(f126,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_7),
% 2.14/0.65    inference(avatar_component_clause,[],[f125])).
% 2.14/0.65  fof(f125,plain,(
% 2.14/0.65    spl6_7 <=> ! [X1,X0] : (m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.14/0.65  fof(f189,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~m1_subset_1(sK5(sK1,X3,sK3(sK0,X2)),u1_struct_0(sK0)) | r2_lattice3(sK1,X3,sK3(sK0,X2)) | ~r2_hidden(sK5(sK1,X3,sK3(sK0,X2)),X2) | ~m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f188])).
% 2.14/0.65  fof(f188,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0)) | r2_lattice3(sK1,X3,sK3(sK0,X2)) | ~r2_hidden(sK5(sK1,X3,sK3(sK0,X2)),X2) | ~m1_subset_1(sK5(sK1,X3,sK3(sK0,X2)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X2),u1_struct_0(sK0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.65    inference(resolution,[],[f184,f149])).
% 2.14/0.65  fof(f149,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r1_orders_2(sK0,X0,sK3(sK0,X1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))) )),
% 2.14/0.65    inference(resolution,[],[f53,f48])).
% 2.14/0.65  fof(f48,plain,(
% 2.14/0.65    ( ! [X0] : (r2_lattice3(sK0,X0,sK3(sK0,X0))) )),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f19,f21,f27])).
% 2.14/0.65  fof(f27,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~v3_lattice3(X0) | r2_lattice3(X0,X1,sK3(X0,X1)) | ~l1_orders_2(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f11])).
% 2.14/0.65  fof(f53,plain,(
% 2.14/0.65    ( ! [X4,X2,X3] : (~r2_lattice3(sK0,X4,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,X4) | r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 2.14/0.65    inference(resolution,[],[f21,f31])).
% 2.14/0.65  fof(f184,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_orders_2(sK0,sK5(sK1,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1)) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f183])).
% 2.14/0.65  fof(f183,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_orders_2(sK0,sK5(sK1,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl6_7 | ~spl6_12)),
% 2.14/0.65    inference(resolution,[],[f181,f126])).
% 2.14/0.65  fof(f181,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK1,X3,X2),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_lattice3(sK1,X3,X2)) ) | ~spl6_12),
% 2.14/0.65    inference(avatar_component_clause,[],[f180])).
% 2.14/0.65  fof(f180,plain,(
% 2.14/0.65    spl6_12 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK1,X3,X2),X2) | ~m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0)) | r2_lattice3(sK1,X3,X2))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.14/0.65  fof(f47,plain,(
% 2.14/0.65    ( ! [X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))) )),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f19,f21,f26])).
% 2.14/0.65  fof(f26,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f11])).
% 2.14/0.65  fof(f19,plain,(
% 2.14/0.65    v3_lattice3(sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f21,plain,(
% 2.14/0.65    l1_orders_2(sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f242,plain,(
% 2.14/0.65    m1_subset_1(sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),u1_struct_0(sK0)) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f21,f206,f233,f32])).
% 2.14/0.65  fof(f32,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f15])).
% 2.14/0.65  fof(f243,plain,(
% 2.14/0.65    r2_hidden(sK5(sK0,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))),sK2(sK1)) | (~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f21,f206,f233,f33])).
% 2.14/0.65  fof(f207,plain,(
% 2.14/0.65    r2_lattice3(sK1,sK2(sK1),sK4(sK1,sK3(sK0,sK2(sK1)))) | (~spl6_7 | ~spl6_8 | ~spl6_12)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f47,f203,f134])).
% 2.14/0.65  fof(f134,plain,(
% 2.14/0.65    ( ! [X0] : (~r2_lattice3(sK1,sK2(sK1),X0) | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_8),
% 2.14/0.65    inference(avatar_component_clause,[],[f133])).
% 2.14/0.65  fof(f133,plain,(
% 2.14/0.65    spl6_8 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0)) | ~r2_lattice3(sK1,sK2(sK1),X0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.14/0.65  fof(f206,plain,(
% 2.14/0.65    m1_subset_1(sK4(sK1,sK3(sK0,sK2(sK1))),u1_struct_0(sK0)) | (~spl6_7 | ~spl6_9 | ~spl6_12)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f47,f203,f156])).
% 2.14/0.65  fof(f156,plain,(
% 2.14/0.65    ( ! [X2] : (m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl6_9),
% 2.14/0.65    inference(avatar_component_clause,[],[f155])).
% 2.14/0.65  fof(f155,plain,(
% 2.14/0.65    spl6_9 <=> ! [X2] : (m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.14/0.65  fof(f182,plain,(
% 2.14/0.65    ~spl6_1 | spl6_12 | ~spl6_7),
% 2.14/0.65    inference(avatar_split_clause,[],[f171,f125,f180,f59])).
% 2.14/0.65  fof(f59,plain,(
% 2.14/0.65    spl6_1 <=> l1_orders_2(sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.14/0.65  fof(f171,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_lattice3(sK1,X3,X2) | ~m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_orders_2(sK0,sK5(sK1,X3,X2),X2)) ) | ~spl6_7),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f170])).
% 2.14/0.65  fof(f170,plain,(
% 2.14/0.65    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_lattice3(sK1,X3,X2) | ~m1_subset_1(sK5(sK1,X3,X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_orders_2(sK0,sK5(sK1,X3,X2),X2)) ) | ~spl6_7),
% 2.14/0.65    inference(resolution,[],[f168,f36])).
% 2.14/0.65  fof(f168,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK1,X0,X1),X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1)) ) | ~spl6_7),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f167])).
% 2.14/0.65  fof(f167,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK1,X0,X1),X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1) | r2_lattice3(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_7),
% 2.14/0.65    inference(resolution,[],[f148,f126])).
% 2.14/0.65  fof(f148,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK1,X1,X0)) )),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f147])).
% 2.14/0.65  fof(f147,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),u1_orders_2(sK0)) | ~m1_subset_1(sK5(sK1,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK1,X1,X0)) )),
% 2.14/0.65    inference(resolution,[],[f86,f82])).
% 2.14/0.65  fof(f82,plain,(
% 2.14/0.65    ( ! [X8,X7] : (~r1_orders_2(sK1,sK5(sK1,X8,X7),X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_lattice3(sK1,X8,X7)) )),
% 2.14/0.65    inference(backward_demodulation,[],[f43,f71])).
% 2.14/0.65  fof(f43,plain,(
% 2.14/0.65    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK5(sK1,X8,X7),X7) | r2_lattice3(sK1,X8,X7)) )),
% 2.14/0.65    inference(resolution,[],[f17,f34])).
% 2.14/0.65  fof(f34,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f15])).
% 2.14/0.65  fof(f176,plain,(
% 2.14/0.65    ~spl6_1 | spl6_11 | ~spl6_10),
% 2.14/0.65    inference(avatar_split_clause,[],[f166,f159,f174,f59])).
% 2.14/0.65  fof(f159,plain,(
% 2.14/0.65    spl6_10 <=> ! [X1,X0] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.14/0.65  fof(f166,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl6_10),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f165])).
% 2.14/0.65  fof(f165,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,X1)) ) | ~spl6_10),
% 2.14/0.65    inference(resolution,[],[f164,f32])).
% 2.14/0.65  fof(f164,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl6_10),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f163])).
% 2.14/0.65  fof(f163,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_orders_2(sK1,sK5(sK0,X0,X1),X1) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl6_10),
% 2.14/0.65    inference(resolution,[],[f160,f119])).
% 2.14/0.65  fof(f119,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK0,X1,X0),X0),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0)) )),
% 2.14/0.65    inference(duplicate_literal_removal,[],[f118])).
% 2.14/0.65  fof(f118,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK5(sK0,X1,X0),X0),u1_orders_2(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0)) )),
% 2.14/0.65    inference(resolution,[],[f56,f55])).
% 2.14/0.65  fof(f55,plain,(
% 2.14/0.65    ( ! [X8,X7] : (~r1_orders_2(sK0,sK5(sK0,X8,X7),X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_lattice3(sK0,X8,X7)) )),
% 2.14/0.65    inference(resolution,[],[f21,f34])).
% 2.14/0.65  fof(f56,plain,(
% 2.14/0.65    ( ! [X10,X9] : (r1_orders_2(sK0,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X9,X10),u1_orders_2(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0))) )),
% 2.14/0.65    inference(resolution,[],[f21,f35])).
% 2.14/0.65  fof(f160,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_10),
% 2.14/0.65    inference(avatar_component_clause,[],[f159])).
% 2.14/0.65  fof(f161,plain,(
% 2.14/0.65    ~spl6_6 | spl6_10),
% 2.14/0.65    inference(avatar_split_clause,[],[f98,f159,f121])).
% 2.14/0.65  fof(f121,plain,(
% 2.14/0.65    spl6_6 <=> l1_orders_2(sK1)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.14/0.65  fof(f98,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~l1_orders_2(sK1) | ~r1_orders_2(sK1,X0,X1)) )),
% 2.14/0.65    inference(forward_demodulation,[],[f97,f71])).
% 2.14/0.65  fof(f97,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~r1_orders_2(sK1,X0,X1)) )),
% 2.14/0.65    inference(forward_demodulation,[],[f96,f71])).
% 2.14/0.65  fof(f96,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~r1_orders_2(sK1,X0,X1)) )),
% 2.14/0.65    inference(superposition,[],[f36,f72])).
% 2.14/0.65  fof(f157,plain,(
% 2.14/0.65    spl6_4 | ~spl6_6 | spl6_9),
% 2.14/0.65    inference(avatar_split_clause,[],[f94,f155,f121,f110])).
% 2.14/0.65  fof(f110,plain,(
% 2.14/0.65    spl6_4 <=> v3_lattice3(sK1)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.14/0.65  fof(f94,plain,(
% 2.14/0.65    ( ! [X2] : (m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X2) | ~l1_orders_2(sK1) | v3_lattice3(sK1)) )),
% 2.14/0.65    inference(superposition,[],[f22,f71])).
% 2.14/0.65  fof(f22,plain,(
% 2.14/0.65    ( ! [X2,X0] : (m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f11])).
% 2.14/0.65  fof(f143,plain,(
% 2.14/0.65    ~spl6_4),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f136])).
% 2.14/0.65  fof(f136,plain,(
% 2.14/0.65    $false | ~spl6_4),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f20,f112])).
% 2.14/0.65  fof(f112,plain,(
% 2.14/0.65    v3_lattice3(sK1) | ~spl6_4),
% 2.14/0.65    inference(avatar_component_clause,[],[f110])).
% 2.14/0.65  fof(f20,plain,(
% 2.14/0.65    ~v3_lattice3(sK1)),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f135,plain,(
% 2.14/0.65    spl6_4 | spl6_8),
% 2.14/0.65    inference(avatar_split_clause,[],[f78,f133,f110])).
% 2.14/0.65  fof(f78,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X0) | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0)) | v3_lattice3(sK1)) )),
% 2.14/0.65    inference(backward_demodulation,[],[f38,f71])).
% 2.14/0.65  fof(f38,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_lattice3(sK1,sK2(sK1),X0) | r2_lattice3(sK1,sK2(sK1),sK4(sK1,X0)) | v3_lattice3(sK1)) )),
% 2.14/0.65    inference(resolution,[],[f17,f23])).
% 2.14/0.65  fof(f23,plain,(
% 2.14/0.65    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | r2_lattice3(X0,sK2(X0),sK4(X0,X2)) | v3_lattice3(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f11])).
% 2.14/0.65  fof(f131,plain,(
% 2.14/0.65    spl6_6),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f128])).
% 2.14/0.65  fof(f128,plain,(
% 2.14/0.65    $false | spl6_6),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f17,f123])).
% 2.14/0.65  fof(f123,plain,(
% 2.14/0.65    ~l1_orders_2(sK1) | spl6_6),
% 2.14/0.65    inference(avatar_component_clause,[],[f121])).
% 2.14/0.65  fof(f127,plain,(
% 2.14/0.65    ~spl6_6 | spl6_7),
% 2.14/0.65    inference(avatar_split_clause,[],[f93,f125,f121])).
% 2.14/0.65  fof(f93,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK1) | r2_lattice3(sK1,X0,X1)) )),
% 2.14/0.65    inference(superposition,[],[f32,f71])).
% 2.14/0.65  fof(f116,plain,(
% 2.14/0.65    spl6_4 | spl6_5),
% 2.14/0.65    inference(avatar_split_clause,[],[f79,f114,f110])).
% 2.14/0.65  fof(f79,plain,(
% 2.14/0.65    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X1) | ~r1_orders_2(sK1,X1,sK4(sK1,X1)) | v3_lattice3(sK1)) )),
% 2.14/0.65    inference(backward_demodulation,[],[f39,f71])).
% 2.14/0.65  fof(f39,plain,(
% 2.14/0.65    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_lattice3(sK1,sK2(sK1),X1) | ~r1_orders_2(sK1,X1,sK4(sK1,X1)) | v3_lattice3(sK1)) )),
% 2.14/0.65    inference(resolution,[],[f17,f24])).
% 2.14/0.65  fof(f24,plain,(
% 2.14/0.65    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~r1_orders_2(X0,X2,sK4(X0,X2)) | v3_lattice3(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f11])).
% 2.14/0.65  fof(f69,plain,(
% 2.14/0.65    spl6_1),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f66])).
% 2.14/0.65  fof(f66,plain,(
% 2.14/0.65    $false | spl6_1),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f21,f61])).
% 2.14/0.65  fof(f61,plain,(
% 2.14/0.65    ~l1_orders_2(sK0) | spl6_1),
% 2.14/0.65    inference(avatar_component_clause,[],[f59])).
% 2.14/0.65  % SZS output end Proof for theBenchmark
% 2.14/0.65  % (16558)------------------------------
% 2.14/0.65  % (16558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (16558)Termination reason: Refutation
% 2.14/0.65  
% 2.14/0.65  % (16558)Memory used [KB]: 6524
% 2.14/0.65  % (16558)Time elapsed: 0.212 s
% 2.14/0.65  % (16558)------------------------------
% 2.14/0.65  % (16558)------------------------------
% 2.14/0.65  % (16553)Success in time 0.286 s
%------------------------------------------------------------------------------
