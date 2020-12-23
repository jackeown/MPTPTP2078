%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1531+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 285 expanded)
%              Number of leaves         :   14 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  361 (1194 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f93,f286,f294,f296,f331,f333])).

fof(f333,plain,
    ( ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f332,f56,f46])).

fof(f46,plain,
    ( spl7_2
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f56,plain,
    ( spl7_4
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f332,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f20,f57])).

fof(f57,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f20,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f331,plain,
    ( spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f329,f48])).

fof(f48,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f329,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f328,f25])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f328,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f327,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f327,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(resolution,[],[f324,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f324,plain,
    ( r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f323,f23])).

fof(f323,plain,
    ( r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(resolution,[],[f306,f53])).

fof(f53,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f306,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,sK2,X1)
        | r1_orders_2(sK0,X1,sK4(sK0,sK1,sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl7_2
    | spl7_10 ),
    inference(subsumption_resolution,[],[f302,f48])).

fof(f302,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK4(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK2,X1)
        | r1_lattice3(sK0,sK1,sK3) )
    | spl7_2
    | spl7_10 ),
    inference(resolution,[],[f300,f211])).

fof(f211,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK4(sK0,X3,sK3),X4)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,sK4(sK0,X3,sK3))
      | ~ r1_lattice3(sK0,X4,X2)
      | r1_lattice3(sK0,X3,sK3) ) ),
    inference(subsumption_resolution,[],[f204,f25])).

fof(f204,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK4(sK0,X3,sK3),X4)
      | r1_orders_2(sK0,X2,sK4(sK0,X3,sK3))
      | ~ r1_lattice3(sK0,X4,X2)
      | r1_lattice3(sK0,X3,sK3) ) ),
    inference(resolution,[],[f26,f111])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | r1_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f110,f25])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | r1_lattice3(sK0,X0,sK3) ) ),
    inference(resolution,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f300,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | spl7_2
    | spl7_10 ),
    inference(subsumption_resolution,[],[f106,f92])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f106,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | spl7_2 ),
    inference(resolution,[],[f105,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f105,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK4(sK0,sK1,sK3),sK2) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_lattice3(sK0,X0,sK3)
      | m1_subset_1(sK4(sK0,X0,sK3),X1) ) ),
    inference(resolution,[],[f97,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,sK3),X0)
      | r1_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f96,f25])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK4(sK0,X0,sK3),X0)
      | r1_lattice3(sK0,X0,sK3) ) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f296,plain,
    ( spl7_2
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f292,f48])).

fof(f292,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f88,f101])).

fof(f101,plain,(
    ! [X2] :
      ( ~ sP6(X2)
      | r1_lattice3(sK0,X2,sK3) ) ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f38,f39_D])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f39_D])).

fof(f39_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f88,plain,
    ( sP6(sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_9
  <=> sP6(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f294,plain,
    ( spl7_4
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f291,f58])).

fof(f58,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f291,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f88,f103])).

fof(f103,plain,(
    ! [X2] :
      ( ~ sP6(X2)
      | r2_lattice3(sK0,X2,sK3) ) ),
    inference(resolution,[],[f99,f40])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,X0,sK3),X0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f98,f25])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK5(sK0,X0,sK3),X0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f286,plain,
    ( ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f284,f58])).

fof(f284,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f283,f25])).

fof(f283,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f282,f23])).

fof(f282,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(resolution,[],[f281,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f281,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f280,f23])).

fof(f280,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_1
    | spl7_4
    | spl7_10 ),
    inference(resolution,[],[f279,f44])).

fof(f44,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl7_1
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f279,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK2,X2)
        | r1_orders_2(sK0,sK5(sK0,sK1,sK3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f277,f58])).

fof(f277,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,sK1,sK3),X2)
        | ~ r2_lattice3(sK0,sK2,X2)
        | r2_lattice3(sK0,sK1,sK3) )
    | spl7_4
    | spl7_10 ),
    inference(resolution,[],[f237,f122])).

fof(f122,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f121,f92])).

fof(f121,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | spl7_4 ),
    inference(resolution,[],[f120,f34])).

fof(f120,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f119,f58])).

fof(f119,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),sK2) ),
    inference(resolution,[],[f102,f60])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_lattice3(sK0,X0,sK3)
      | m1_subset_1(sK5(sK0,X0,sK3),X1) ) ),
    inference(resolution,[],[f99,f37])).

fof(f237,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(sK5(sK0,X14,sK3),X15)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK5(sK0,X14,sK3),X13)
      | ~ r2_lattice3(sK0,X15,X13)
      | r2_lattice3(sK0,X14,sK3) ) ),
    inference(subsumption_resolution,[],[f230,f25])).

fof(f230,plain,(
    ! [X14,X15,X13] :
      ( ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK5(sK0,X14,sK3),X15)
      | r1_orders_2(sK0,sK5(sK0,X14,sK3),X13)
      | ~ r2_lattice3(sK0,X15,X13)
      | r2_lattice3(sK0,X14,sK3) ) ),
    inference(resolution,[],[f30,f148])).

fof(f148,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f145,f25])).

fof(f145,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f83,f90,f86])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK2)
    | sP6(sK1) ),
    inference(resolution,[],[f39,f60])).

fof(f59,plain,
    ( ~ spl7_4
    | spl7_3 ),
    inference(avatar_split_clause,[],[f22,f51,f56])).

fof(f22,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f21,f51,f42])).

fof(f21,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f19,f46,f42])).

fof(f19,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
