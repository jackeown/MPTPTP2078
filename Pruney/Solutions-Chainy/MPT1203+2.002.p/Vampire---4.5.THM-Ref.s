%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  106 (1685 expanded)
%              Number of leaves         :   18 ( 736 expanded)
%              Depth                    :   17
%              Number of atoms          :  461 (15364 expanded)
%              Number of equality atoms :  121 (5429 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(subsumption_resolution,[],[f348,f56])).

fof(f56,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK2 != sK3
    & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                    & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                  & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3)
              & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

% (4766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3)
            & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( sK2 != X3
          & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2)
          & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( sK2 != X3
        & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2)
        & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( sK2 != sK3
      & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
      & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (4774)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

fof(f348,plain,(
    sK2 = sK3 ),
    inference(forward_demodulation,[],[f347,f323])).

fof(f323,plain,(
    sK2 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f322,f134])).

fof(f134,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f117,f131])).

fof(f131,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f52,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f50,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f50,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
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

fof(f48,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f52,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f322,plain,(
    sK2 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f321,f266])).

fof(f266,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f265,f173])).

fof(f173,plain,(
    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f168,f134])).

fof(f168,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f51,f52,f83,f63])).

fof(f63,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f83,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f50,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f265,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f264,f249])).

fof(f249,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f216,f240])).

fof(f240,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f237,f55])).

fof(f55,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f237,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f53,f75])).

fof(f53,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f216,plain,(
    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f53,f72])).

fof(f264,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f263,f226])).

fof(f226,plain,(
    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f73])).

% (4766)Refutation not found, incomplete strategy% (4766)------------------------------
% (4766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (4766)Termination reason: Refutation not found, incomplete strategy

% (4766)Memory used [KB]: 10618
% (4766)Time elapsed: 0.079 s
% (4766)------------------------------
% (4766)------------------------------
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f79,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f50,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f263,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f210,f133])).

fof(f133,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f121,f127])).

% (4777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f127,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f52,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f121,plain,(
    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f52,f73])).

fof(f210,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f49,f51,f52,f53,f67])).

fof(f67,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0)))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

% (4777)Refutation not found, incomplete strategy% (4777)------------------------------
% (4777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4777)Termination reason: Refutation not found, incomplete strategy

% (4777)Memory used [KB]: 6140
% (4777)Time elapsed: 0.002 s
% (4777)------------------------------
% (4777)------------------------------
fof(f49,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f321,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f320,f245])).

fof(f245,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f223,f232])).

fof(f232,plain,(
    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f74])).

fof(f223,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f73])).

fof(f320,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f192,f246])).

fof(f246,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f222,f242])).

fof(f242,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f231,f54])).

fof(f54,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f231,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f53,f74])).

fof(f222,plain,(
    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f53,f73])).

fof(f192,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f49,f51,f52,f53,f67])).

fof(f347,plain,(
    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f183,f249])).

fof(f183,plain,(
    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f83,f51,f53,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n002.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.25  % CPULimit   : 60
% 0.10/0.25  % WCLimit    : 600
% 0.10/0.25  % DateTime   : Tue Dec  1 09:48:51 EST 2020
% 0.10/0.26  % CPUTime    : 
% 0.11/0.35  % (4779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.11/0.35  % (4771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.11/0.38  % (4765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.11/0.38  % (4780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.11/0.39  % (4775)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.11/0.39  % (4770)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.11/0.39  % (4767)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.11/0.39  % (4785)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.11/0.39  % (4780)Refutation found. Thanks to Tanya!
% 0.11/0.39  % SZS status Theorem for theBenchmark
% 0.11/0.39  % SZS output start Proof for theBenchmark
% 0.11/0.39  fof(f349,plain,(
% 0.11/0.39    $false),
% 0.11/0.39    inference(subsumption_resolution,[],[f348,f56])).
% 0.11/0.39  fof(f56,plain,(
% 0.11/0.39    sK2 != sK3),
% 0.11/0.39    inference(cnf_transformation,[],[f35])).
% 0.11/0.39  fof(f35,plain,(
% 0.11/0.39    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.11/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).
% 0.11/0.39  fof(f31,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f32,plain,(
% 0.11/0.39    ? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  % (4766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.39  fof(f33,plain,(
% 0.11/0.39    ? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f34,plain,(
% 0.11/0.39    ? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f15,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.11/0.39    inference(flattening,[],[f14])).
% 0.11/0.39  fof(f14,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f10])).
% 0.11/0.39  % (4774)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.11/0.39  fof(f10,negated_conjecture,(
% 0.11/0.39    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.11/0.39    inference(negated_conjecture,[],[f9])).
% 0.11/0.40  fof(f9,conjecture,(
% 0.11/0.40    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).
% 0.11/0.40  fof(f348,plain,(
% 0.11/0.40    sK2 = sK3),
% 0.11/0.40    inference(forward_demodulation,[],[f347,f323])).
% 0.11/0.40  fof(f323,plain,(
% 0.11/0.40    sK2 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f322,f134])).
% 0.11/0.40  fof(f134,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f117,f131])).
% 0.11/0.40  fof(f131,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f52,f75])).
% 0.11/0.40  fof(f75,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f30])).
% 0.11/0.40  fof(f30,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f29])).
% 0.11/0.40  fof(f29,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f2])).
% 0.11/0.40  fof(f2,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.11/0.40  fof(f52,plain,(
% 0.11/0.40    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f51,plain,(
% 0.11/0.40    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f80,plain,(
% 0.11/0.40    l2_lattices(sK0)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f50,f58])).
% 0.11/0.40  fof(f58,plain,(
% 0.11/0.40    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f16])).
% 0.11/0.40  fof(f16,plain,(
% 0.11/0.40    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f6])).
% 0.11/0.40  fof(f6,axiom,(
% 0.11/0.40    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.11/0.40  fof(f50,plain,(
% 0.11/0.40    l3_lattices(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f81,plain,(
% 0.11/0.40    v4_lattices(sK0)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f48,f50,f60])).
% 0.11/0.40  fof(f60,plain,(
% 0.11/0.40    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f18])).
% 0.11/0.40  fof(f18,plain,(
% 0.11/0.40    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.11/0.40    inference(flattening,[],[f17])).
% 0.11/0.40  fof(f17,plain,(
% 0.11/0.40    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f13])).
% 0.11/0.40  fof(f13,plain,(
% 0.11/0.40    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.11/0.40    inference(pure_predicate_removal,[],[f12])).
% 0.11/0.40  fof(f12,plain,(
% 0.11/0.40    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.11/0.40    inference(pure_predicate_removal,[],[f11])).
% 0.11/0.40  fof(f11,plain,(
% 0.11/0.40    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.11/0.40    inference(pure_predicate_removal,[],[f1])).
% 0.11/0.40  fof(f1,axiom,(
% 0.11/0.40    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.11/0.40  fof(f48,plain,(
% 0.11/0.40    v10_lattices(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f47,plain,(
% 0.11/0.40    ~v2_struct_0(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f117,plain,(
% 0.11/0.40    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f52,f72])).
% 0.11/0.40  fof(f72,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f24])).
% 0.11/0.40  fof(f24,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f23])).
% 0.11/0.40  fof(f23,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f7])).
% 0.11/0.40  fof(f7,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.11/0.40  fof(f322,plain,(
% 0.11/0.40    sK2 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1))),
% 0.11/0.40    inference(forward_demodulation,[],[f321,f266])).
% 0.11/0.40  fof(f266,plain,(
% 0.11/0.40    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f265,f173])).
% 0.11/0.40  fof(f173,plain,(
% 0.11/0.40    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f168,f134])).
% 0.11/0.40  fof(f168,plain,(
% 0.11/0.40    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1))),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f50,f51,f52,f83,f63])).
% 0.11/0.40  fof(f63,plain,(
% 0.11/0.40    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f40])).
% 0.11/0.40  fof(f40,plain,(
% 0.11/0.40    ! [X0] : (((v9_lattices(X0) | ((sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).
% 0.11/0.40  fof(f38,plain,(
% 0.11/0.40    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f39,plain,(
% 0.11/0.40    ! [X0] : (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f37,plain,(
% 0.11/0.40    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(rectify,[],[f36])).
% 0.11/0.40  fof(f36,plain,(
% 0.11/0.40    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(nnf_transformation,[],[f20])).
% 0.11/0.40  fof(f20,plain,(
% 0.11/0.40    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f19])).
% 0.11/0.40  fof(f19,plain,(
% 0.11/0.40    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f5])).
% 0.11/0.40  fof(f5,axiom,(
% 0.11/0.40    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.11/0.40  fof(f83,plain,(
% 0.11/0.40    v9_lattices(sK0)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f48,f50,f62])).
% 0.11/0.40  fof(f62,plain,(
% 0.11/0.40    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f18])).
% 0.11/0.40  fof(f265,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f264,f249])).
% 0.11/0.40  fof(f249,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f216,f240])).
% 0.11/0.40  fof(f240,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f237,f55])).
% 0.11/0.40  fof(f55,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f237,plain,(
% 0.11/0.40    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f53,f75])).
% 0.11/0.40  fof(f53,plain,(
% 0.11/0.40    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f216,plain,(
% 0.11/0.40    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f81,f80,f51,f53,f72])).
% 0.11/0.40  fof(f264,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f263,f226])).
% 0.11/0.40  fof(f226,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f73])).
% 0.11/0.40  % (4766)Refutation not found, incomplete strategy% (4766)------------------------------
% 0.11/0.40  % (4766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  fof(f73,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f26])).
% 0.11/0.40  % (4766)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (4766)Memory used [KB]: 10618
% 0.11/0.40  % (4766)Time elapsed: 0.079 s
% 0.11/0.40  % (4766)------------------------------
% 0.11/0.40  % (4766)------------------------------
% 0.11/0.40  fof(f26,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f25])).
% 0.11/0.40  fof(f25,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f8])).
% 0.11/0.40  fof(f8,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.11/0.40  fof(f79,plain,(
% 0.11/0.40    l1_lattices(sK0)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f50,f57])).
% 0.11/0.40  fof(f57,plain,(
% 0.11/0.40    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f16])).
% 0.11/0.40  fof(f82,plain,(
% 0.11/0.40    v6_lattices(sK0)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f48,f50,f61])).
% 0.11/0.40  fof(f61,plain,(
% 0.11/0.40    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f18])).
% 0.11/0.40  fof(f263,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f210,f133])).
% 0.11/0.40  fof(f133,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f121,f127])).
% 0.11/0.40  % (4777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.40  fof(f127,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f52,f74])).
% 0.11/0.40  fof(f74,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f28])).
% 0.11/0.40  fof(f28,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f27])).
% 0.11/0.40  fof(f27,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f3])).
% 0.11/0.40  fof(f3,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.11/0.40  fof(f121,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f52,f73])).
% 0.11/0.40  fof(f210,plain,(
% 0.11/0.40    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1))),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f50,f49,f51,f52,f53,f67])).
% 0.11/0.40  fof(f67,plain,(
% 0.11/0.40    ( ! [X6,X4,X0,X5] : (~v11_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f46])).
% 0.11/0.40  fof(f46,plain,(
% 0.11/0.40    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).
% 0.11/0.40  fof(f43,plain,(
% 0.11/0.40    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f44,plain,(
% 0.11/0.40    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f45,plain,(
% 0.11/0.40    ! [X0] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f42,plain,(
% 0.11/0.40    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(rectify,[],[f41])).
% 0.11/0.40  fof(f41,plain,(
% 0.11/0.40    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(nnf_transformation,[],[f22])).
% 0.11/0.40  fof(f22,plain,(
% 0.11/0.40    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.11/0.40    inference(flattening,[],[f21])).
% 0.11/0.40  fof(f21,plain,(
% 0.11/0.40    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f4])).
% 0.11/0.40  fof(f4,axiom,(
% 0.11/0.40    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 0.11/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).
% 0.11/0.40  % (4777)Refutation not found, incomplete strategy% (4777)------------------------------
% 0.11/0.40  % (4777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (4777)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (4777)Memory used [KB]: 6140
% 0.11/0.40  % (4777)Time elapsed: 0.002 s
% 0.11/0.40  % (4777)------------------------------
% 0.11/0.40  % (4777)------------------------------
% 0.11/0.40  fof(f49,plain,(
% 0.11/0.40    v11_lattices(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f321,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f320,f245])).
% 0.11/0.40  fof(f245,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.11/0.40    inference(forward_demodulation,[],[f223,f232])).
% 0.11/0.40  fof(f232,plain,(
% 0.11/0.40    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f74])).
% 0.11/0.40  fof(f223,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f52,f53,f73])).
% 0.11/0.40  fof(f320,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f192,f246])).
% 0.11/0.40  fof(f246,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f222,f242])).
% 0.11/0.40  fof(f242,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(forward_demodulation,[],[f231,f54])).
% 0.11/0.40  fof(f54,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.11/0.40    inference(cnf_transformation,[],[f35])).
% 0.11/0.40  fof(f231,plain,(
% 0.11/0.40    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f53,f74])).
% 0.11/0.40  fof(f222,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1)),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f82,f79,f51,f53,f73])).
% 0.11/0.40  fof(f192,plain,(
% 0.11/0.40    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1))),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f50,f49,f51,f52,f53,f67])).
% 0.11/0.40  fof(f347,plain,(
% 0.11/0.40    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.11/0.40    inference(forward_demodulation,[],[f183,f249])).
% 0.11/0.40  fof(f183,plain,(
% 0.11/0.40    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1))),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f47,f50,f83,f51,f53,f63])).
% 0.11/0.40  % SZS output end Proof for theBenchmark
% 0.11/0.40  % (4780)------------------------------
% 0.11/0.40  % (4780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (4780)Termination reason: Refutation
% 0.11/0.40  
% 0.11/0.40  % (4780)Memory used [KB]: 6396
% 0.11/0.40  % (4780)Time elapsed: 0.018 s
% 0.11/0.40  % (4780)------------------------------
% 0.11/0.40  % (4780)------------------------------
% 0.11/0.40  % (4761)Success in time 0.131 s
%------------------------------------------------------------------------------
