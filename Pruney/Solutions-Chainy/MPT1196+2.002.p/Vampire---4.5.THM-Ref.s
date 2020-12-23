%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 276 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   32
%              Number of atoms          :  370 (1815 expanded)
%              Number of equality atoms :   51 (  51 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

fof(f152,plain,(
    ~ l3_lattices(sK0) ),
    inference(resolution,[],[f151,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f151,plain,(
    ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f150,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f149,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f148,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f146,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f146,plain,
    ( ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f145,f37])).

fof(f145,plain,
    ( ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f41])).

fof(f144,plain,
    ( ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f43])).

fof(f43,plain,(
    ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,
    ( r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2)
    | r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f46,f137])).

% (19252)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f137,plain,(
    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f136,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f97,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0)))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0)))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f97,plain,(
    ! [X1] :
      ( k1_lattices(sK0,X1,sK2) = k1_lattices(sK0,k2_lattices(sK0,sK1,k1_lattices(sK0,X1,sK2)),k1_lattices(sK0,X1,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,X1,X0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k1_lattices(sK0,X1,X0)),k1_lattices(sK0,X1,X0)) ) ),
    inference(resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,X0,X1) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X0,X1)),k1_lattices(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(sK0,X0,X1) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X0,X1)),k1_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X4,X2,X3] :
      ( ~ l2_lattices(sK0)
      | k1_lattices(sK0,X3,X4) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X3,X4)),k1_lattices(sK0,X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f66,f37])).

fof(f66,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,X3,X4) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X3,X4)),k1_lattices(sK0,X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f63,f55])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f62,f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK6(X0) != k1_lattices(X0,k2_lattices(X0,sK5(X0),sK6(X0)),sK6(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK5(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK5(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK6(X0) != k1_lattices(X0,k2_lattices(X0,sK5(X0),sK6(X0)),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (19250)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (19248)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (19251)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (19244)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (19258)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (19256)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (19256)Refutation not found, incomplete strategy% (19256)------------------------------
% 0.21/0.50  % (19256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19256)Memory used [KB]: 1663
% 0.21/0.50  % (19256)Time elapsed: 0.075 s
% 0.21/0.50  % (19256)------------------------------
% 0.21/0.50  % (19256)------------------------------
% 0.21/0.50  % (19248)Refutation not found, incomplete strategy% (19248)------------------------------
% 0.21/0.50  % (19248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19248)Memory used [KB]: 10618
% 0.21/0.50  % (19248)Time elapsed: 0.071 s
% 0.21/0.50  % (19248)------------------------------
% 0.21/0.50  % (19248)------------------------------
% 0.21/0.50  % (19250)Refutation not found, incomplete strategy% (19250)------------------------------
% 0.21/0.50  % (19250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19250)Memory used [KB]: 10618
% 0.21/0.50  % (19250)Time elapsed: 0.082 s
% 0.21/0.50  % (19250)------------------------------
% 0.21/0.50  % (19250)------------------------------
% 0.21/0.50  % (19259)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (19259)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    l3_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ((~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X2] : (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~l3_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f151,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~l2_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f149,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f146,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f37])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f41])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2) | r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(superposition,[],[f46,f137])).
% 0.21/0.51  % (19252)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f42])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f41])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(superposition,[],[f97,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f57,f37])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f40])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f47,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v9_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (((v9_lattices(X0) | ((sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK3(X0) != k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X1] : (k1_lattices(sK0,X1,sK2) = k1_lattices(sK0,k2_lattices(sK0,sK1,k1_lattices(sK0,X1,sK2)),k1_lattices(sK0,X1,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(resolution,[],[f88,f42])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k1_lattices(sK0,X1,X0)),k1_lattices(sK0,X1,X0))) )),
% 0.21/0.51    inference(resolution,[],[f87,f41])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X0,X1) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X0,X1)),k1_lattices(sK0,X0,X1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f40])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_lattices(sK0,X0,X1) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X0,X1)),k1_lattices(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f71,f44])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~l2_lattices(sK0) | k1_lattices(sK0,X3,X4) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X3,X4)),k1_lattices(sK0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f37])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X4) = k1_lattices(sK0,k2_lattices(sK0,X2,k1_lattices(sK0,X3,X4)),k1_lattices(sK0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f63,f55])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f62,f37])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f61,f40])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f51,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v8_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ((sK6(X0) != k1_lattices(X0,k2_lattices(X0,sK5(X0),sK6(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f35,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK5(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK5(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK6(X0) != k1_lattices(X0,k2_lattices(X0,sK5(X0),sK6(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (19259)------------------------------
% 0.21/0.51  % (19259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19259)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (19259)Memory used [KB]: 6268
% 0.21/0.51  % (19259)Time elapsed: 0.084 s
% 0.21/0.51  % (19259)------------------------------
% 0.21/0.51  % (19259)------------------------------
% 0.21/0.51  % (19239)Success in time 0.146 s
%------------------------------------------------------------------------------
