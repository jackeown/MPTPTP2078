%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1496+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 732 expanded)
%              Number of leaves         :    9 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          :  312 (4913 expanded)
%              Number of equality atoms :   16 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4772,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3240,f3241,f4750,f4762])).

fof(f4762,plain,
    ( ~ spl35_1
    | spl35_2 ),
    inference(avatar_contradiction_clause,[],[f4761])).

fof(f4761,plain,
    ( $false
    | ~ spl35_1
    | spl35_2 ),
    inference(subsumption_resolution,[],[f4760,f3234])).

fof(f3234,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,sK4)
    | ~ spl35_1 ),
    inference(avatar_component_clause,[],[f3233])).

fof(f3233,plain,
    ( spl35_1
  <=> r1_lattice3(k3_lattice3(sK3),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_1])])).

fof(f4760,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,sK4)
    | spl35_2 ),
    inference(forward_demodulation,[],[f4759,f4335])).

fof(f4335,plain,(
    sK4 = k4_lattice3(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4334,f3091])).

fof(f3091,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3009])).

fof(f3009,plain,
    ( ( ~ r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
      | ~ r1_lattice3(k3_lattice3(sK3),sK2,sK4) )
    & ( r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
      | r1_lattice3(k3_lattice3(sK3),sK2,sK4) )
    & m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    & l3_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3006,f3008,f3007])).

fof(f3007,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r1_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r3_lattice3(sK3,k5_lattice3(sK3,X2),sK2)
            | ~ r1_lattice3(k3_lattice3(sK3),sK2,X2) )
          & ( r3_lattice3(sK3,k5_lattice3(sK3,X2),sK2)
            | r1_lattice3(k3_lattice3(sK3),sK2,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3))) )
      & l3_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3008,plain,
    ( ? [X2] :
        ( ( ~ r3_lattice3(sK3,k5_lattice3(sK3,X2),sK2)
          | ~ r1_lattice3(k3_lattice3(sK3),sK2,X2) )
        & ( r3_lattice3(sK3,k5_lattice3(sK3,X2),sK2)
          | r1_lattice3(k3_lattice3(sK3),sK2,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3))) )
   => ( ( ~ r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
        | ~ r1_lattice3(k3_lattice3(sK3),sK2,sK4) )
      & ( r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
        | r1_lattice3(k3_lattice3(sK3),sK2,sK4) )
      & m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f3006,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r1_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f3005])).

fof(f3005,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r1_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2921])).

fof(f2921,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <~> r3_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f2920])).

fof(f2920,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <~> r3_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2896])).

fof(f2896,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
           => ( r1_lattice3(k3_lattice3(X1),X0,X2)
            <=> r3_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2895])).

fof(f2895,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <=> r3_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_lattice3)).

fof(f4334,plain,
    ( sK4 = k4_lattice3(sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f4333,f3092])).

fof(f3092,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4333,plain,
    ( sK4 = k4_lattice3(sK3,sK4)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f4174,f3093])).

fof(f3093,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f3009])).

fof(f4174,plain,
    ( sK4 = k4_lattice3(sK3,sK4)
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f3616,f3189])).

fof(f3189,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2979])).

fof(f2979,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2978])).

fof(f2978,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2822])).

fof(f2822,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(f3616,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f3615,f3612])).

fof(f3612,plain,(
    sK4 = k5_lattice3(sK3,sK4) ),
    inference(subsumption_resolution,[],[f3611,f3091])).

fof(f3611,plain,
    ( sK4 = k5_lattice3(sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f3610,f3092])).

fof(f3610,plain,
    ( sK4 = k5_lattice3(sK3,sK4)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f3500,f3093])).

fof(f3500,plain,
    ( sK4 = k5_lattice3(sK3,sK4)
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f3094,f3104])).

fof(f3104,plain,(
    ! [X0,X1] :
      ( k5_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2929])).

fof(f2929,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2928])).

fof(f2928,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2823])).

fof(f2823,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(f3094,plain,(
    m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) ),
    inference(cnf_transformation,[],[f3009])).

fof(f3615,plain,(
    m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f3614,f3091])).

fof(f3614,plain,
    ( m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f3613,f3092])).

fof(f3613,plain,
    ( m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f3501,f3093])).

fof(f3501,plain,
    ( m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f3094,f3103])).

fof(f3103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2927])).

fof(f2927,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2926])).

fof(f2926,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2839])).

fof(f2839,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(f4759,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | spl35_2 ),
    inference(subsumption_resolution,[],[f4758,f3091])).

fof(f4758,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | v2_struct_0(sK3)
    | spl35_2 ),
    inference(subsumption_resolution,[],[f4757,f3092])).

fof(f4757,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_2 ),
    inference(subsumption_resolution,[],[f4756,f3093])).

fof(f4756,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_2 ),
    inference(subsumption_resolution,[],[f4752,f3616])).

fof(f4752,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_2 ),
    inference(resolution,[],[f4751,f3106])).

fof(f3106,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f3015])).

fof(f3015,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_lattice3(X1,X2,X0)
              | ~ r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r3_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2931])).

fof(f2931,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f2930])).

fof(f2930,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2894])).

fof(f2894,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_lattice3)).

fof(f4751,plain,
    ( ~ r3_lattice3(sK3,sK4,sK2)
    | spl35_2 ),
    inference(forward_demodulation,[],[f3239,f3612])).

fof(f3239,plain,
    ( ~ r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
    | spl35_2 ),
    inference(avatar_component_clause,[],[f3237])).

fof(f3237,plain,
    ( spl35_2
  <=> r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_2])])).

fof(f4750,plain,
    ( spl35_1
    | ~ spl35_2 ),
    inference(avatar_contradiction_clause,[],[f4749])).

fof(f4749,plain,
    ( $false
    | spl35_1
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f4748,f3091])).

fof(f4748,plain,
    ( v2_struct_0(sK3)
    | spl35_1
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f4747,f3092])).

fof(f4747,plain,
    ( ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_1
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f4746,f3093])).

fof(f4746,plain,
    ( ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_1
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f4745,f3616])).

fof(f4745,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl35_1
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f4739,f3235])).

fof(f3235,plain,
    ( ~ r1_lattice3(k3_lattice3(sK3),sK2,sK4)
    | spl35_1 ),
    inference(avatar_component_clause,[],[f3233])).

fof(f4739,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ spl35_2 ),
    inference(superposition,[],[f3967,f3189])).

fof(f3967,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f3966,f3616])).

fof(f3966,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ spl35_2 ),
    inference(forward_demodulation,[],[f3965,f3612])).

fof(f3965,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ spl35_2 ),
    inference(forward_demodulation,[],[f3964,f3612])).

fof(f3964,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,k5_lattice3(sK3,sK4)))
    | ~ m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f3963,f3091])).

fof(f3963,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,k5_lattice3(sK3,sK4)))
    | ~ m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f3962,f3092])).

fof(f3962,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,k5_lattice3(sK3,sK4)))
    | ~ m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ spl35_2 ),
    inference(subsumption_resolution,[],[f3959,f3093])).

fof(f3959,plain,
    ( r1_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,k5_lattice3(sK3,sK4)))
    | ~ m1_subset_1(k5_lattice3(sK3,sK4),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ spl35_2 ),
    inference(resolution,[],[f3238,f3105])).

fof(f3105,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f3015])).

fof(f3238,plain,
    ( r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
    | ~ spl35_2 ),
    inference(avatar_component_clause,[],[f3237])).

fof(f3241,plain,
    ( spl35_1
    | spl35_2 ),
    inference(avatar_split_clause,[],[f3095,f3237,f3233])).

fof(f3095,plain,
    ( r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
    | r1_lattice3(k3_lattice3(sK3),sK2,sK4) ),
    inference(cnf_transformation,[],[f3009])).

fof(f3240,plain,
    ( ~ spl35_1
    | ~ spl35_2 ),
    inference(avatar_split_clause,[],[f3096,f3237,f3233])).

fof(f3096,plain,
    ( ~ r3_lattice3(sK3,k5_lattice3(sK3,sK4),sK2)
    | ~ r1_lattice3(k3_lattice3(sK3),sK2,sK4) ),
    inference(cnf_transformation,[],[f3009])).
%------------------------------------------------------------------------------
