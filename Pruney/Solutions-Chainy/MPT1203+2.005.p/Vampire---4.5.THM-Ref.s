%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   98 (2001 expanded)
%              Number of leaves         :   15 ( 872 expanded)
%              Depth                    :   19
%              Number of atoms          :  409 (18238 expanded)
%              Number of equality atoms :  101 (6415 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1090,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1089,f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

fof(f1089,plain,(
    sK2 = sK3 ),
    inference(forward_demodulation,[],[f1088,f146])).

fof(f146,plain,(
    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f44,f46,f45,f74,f58])).

fof(f58,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f74,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f41,f42,f44,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
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
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
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
       => ( v8_lattices(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f42,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1088,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f1050,f1085])).

fof(f1085,plain,(
    sK3 = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f1068,f1079])).

fof(f1079,plain,(
    sK3 = k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1078,f221])).

fof(f221,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f182,f214])).

fof(f214,plain,(
    k2_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f194,f122])).

fof(f122,plain,(
    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f111])).

fof(f111,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f70,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

% (13146)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f16,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f73,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f41,f42,f44,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f194,plain,(
    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f47,f63])).

fof(f47,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f182,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f41,f44,f74,f45,f47,f58])).

fof(f1078,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f1051,f1070])).

fof(f1070,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f1069,f276])).

fof(f276,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k2_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f275,f111])).

fof(f275,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f274,f236])).

fof(f236,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f235,f122])).

fof(f235,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f171,f119])).

fof(f119,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f45,f46,f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f71,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f41,f42,f44,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f46,f45,f47,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (13146)Refutation not found, incomplete strategy% (13146)------------------------------
% (13146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13136)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (13146)Termination reason: Refutation not found, incomplete strategy
% (13135)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark

% (13146)Memory used [KB]: 10618
% (13146)Time elapsed: 0.135 s
% (13146)------------------------------
% (13146)------------------------------
% (13134)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f8,axiom,(
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
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

fof(f43,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f274,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f273,f209])).

fof(f209,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f206,f49])).

fof(f49,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f206,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f45,f47,f65])).

fof(f273,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f153,f207])).

fof(f207,plain,(
    k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f47,f65])).

fof(f153,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f46,f45,f47,f57])).

fof(f1069,plain,(
    k3_lattices(sK0,sK3,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f47,f124,f65])).

fof(f124,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f107,f111])).

fof(f107,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f46,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f1051,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f47,f124,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f1068,plain,(
    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f124,f65])).

fof(f1050,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f124,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13131)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (13132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (13141)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (13139)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (13140)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (13133)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.54  % (13139)Refutation not found, incomplete strategy% (13139)------------------------------
% 0.21/0.54  % (13139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13126)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (13137)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (13127)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13138)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (13138)Refutation not found, incomplete strategy% (13138)------------------------------
% 0.21/0.55  % (13138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13138)Memory used [KB]: 6012
% 0.21/0.55  % (13138)Time elapsed: 0.002 s
% 0.21/0.55  % (13138)------------------------------
% 0.21/0.55  % (13138)------------------------------
% 0.21/0.55  % (13144)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.55  % (13130)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.55  % (13128)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.42/0.56  % (13142)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.42/0.56  % (13139)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (13139)Memory used [KB]: 2174
% 1.42/0.56  % (13139)Time elapsed: 0.106 s
% 1.42/0.56  % (13139)------------------------------
% 1.42/0.56  % (13139)------------------------------
% 1.42/0.56  % (13143)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.42/0.56  % (13129)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.42/0.56  % (13141)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f1090,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(subsumption_resolution,[],[f1089,f50])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    sK2 != sK3),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    ? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f15,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f14])).
% 1.42/0.56  fof(f14,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,negated_conjecture,(
% 1.42/0.56    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 1.42/0.56    inference(negated_conjecture,[],[f9])).
% 1.42/0.56  fof(f9,conjecture,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).
% 1.42/0.56  fof(f1089,plain,(
% 1.42/0.56    sK2 = sK3),
% 1.42/0.56    inference(forward_demodulation,[],[f1088,f146])).
% 1.42/0.56  fof(f146,plain,(
% 1.42/0.56    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f44,f46,f45,f74,f58])).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f40])).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ! [X0] : (((v8_lattices(X0) | ((sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).
% 1.42/0.56  fof(f38,plain,(
% 1.42/0.56    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f39,plain,(
% 1.42/0.56    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(rectify,[],[f36])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 1.42/0.56  fof(f74,plain,(
% 1.42/0.56    v8_lattices(sK0)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f42,f44,f56])).
% 1.42/0.56  fof(f56,plain,(
% 1.42/0.56    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f18,plain,(
% 1.42/0.56    ! [X0] : ((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.42/0.56    inference(flattening,[],[f17])).
% 1.42/0.56  fof(f17,plain,(
% 1.42/0.56    ! [X0] : (((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f13])).
% 1.42/0.56  fof(f13,plain,(
% 1.42/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.56    inference(pure_predicate_removal,[],[f12])).
% 1.42/0.56  fof(f12,plain,(
% 1.42/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.56    inference(pure_predicate_removal,[],[f11])).
% 1.42/0.56  fof(f11,plain,(
% 1.42/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.56    inference(pure_predicate_removal,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    v10_lattices(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    l3_lattices(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ~v2_struct_0(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f1088,plain,(
% 1.42/0.56    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.42/0.56    inference(forward_demodulation,[],[f1050,f1085])).
% 1.42/0.56  fof(f1085,plain,(
% 1.42/0.56    sK3 = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.42/0.56    inference(backward_demodulation,[],[f1068,f1079])).
% 1.42/0.56  fof(f1079,plain,(
% 1.42/0.56    sK3 = k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2))),
% 1.42/0.56    inference(forward_demodulation,[],[f1078,f221])).
% 1.42/0.56  fof(f221,plain,(
% 1.42/0.56    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3)),
% 1.42/0.56    inference(forward_demodulation,[],[f182,f214])).
% 1.42/0.56  fof(f214,plain,(
% 1.42/0.56    k2_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3)),
% 1.42/0.56    inference(forward_demodulation,[],[f194,f122])).
% 1.42/0.56  fof(f122,plain,(
% 1.42/0.56    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK2)),
% 1.42/0.56    inference(backward_demodulation,[],[f48,f111])).
% 1.42/0.56  fof(f111,plain,(
% 1.42/0.56    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f46,f63])).
% 1.42/0.56  fof(f63,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f26])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f25])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f7])).
% 1.42/0.56  fof(f7,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.42/0.56  fof(f70,plain,(
% 1.42/0.56    l1_lattices(sK0)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f44,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f16])).
% 1.42/0.56  % (13146)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.42/0.56  fof(f16,plain,(
% 1.42/0.56    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.42/0.56  fof(f73,plain,(
% 1.42/0.56    v6_lattices(sK0)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f42,f44,f55])).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f194,plain,(
% 1.42/0.56    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f47,f63])).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.42/0.56    inference(cnf_transformation,[],[f35])).
% 1.42/0.56  fof(f182,plain,(
% 1.42/0.56    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f44,f74,f45,f47,f58])).
% 1.42/0.56  fof(f1078,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3)),
% 1.42/0.56    inference(forward_demodulation,[],[f1051,f1070])).
% 1.42/0.56  fof(f1070,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3)),
% 1.42/0.56    inference(forward_demodulation,[],[f1069,f276])).
% 1.42/0.56  fof(f276,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k2_lattices(sK0,sK1,sK2))),
% 1.42/0.56    inference(forward_demodulation,[],[f275,f111])).
% 1.42/0.56  fof(f275,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))),
% 1.42/0.56    inference(forward_demodulation,[],[f274,f236])).
% 1.42/0.56  fof(f236,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))),
% 1.42/0.56    inference(forward_demodulation,[],[f235,f122])).
% 1.42/0.56  fof(f235,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))),
% 1.42/0.56    inference(forward_demodulation,[],[f171,f119])).
% 1.42/0.56  fof(f119,plain,(
% 1.42/0.56    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f72,f71,f45,f46,f65])).
% 1.42/0.56  fof(f65,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f30])).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f29])).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 1.42/0.56  fof(f71,plain,(
% 1.42/0.56    l2_lattices(sK0)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f44,f52])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f16])).
% 1.42/0.56  fof(f72,plain,(
% 1.42/0.56    v4_lattices(sK0)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f42,f44,f54])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f171,plain,(
% 1.42/0.56    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f46,f45,f47,f57])).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (~v11_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f20])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f19])).
% 1.42/0.56  fof(f19,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f8])).
% 1.42/0.56  % (13146)Refutation not found, incomplete strategy% (13146)------------------------------
% 1.42/0.56  % (13146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (13136)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.42/0.57  % (13146)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  % (13135)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.42/0.57  
% 1.42/0.57  % (13146)Memory used [KB]: 10618
% 1.42/0.57  % (13146)Time elapsed: 0.135 s
% 1.42/0.57  % (13146)------------------------------
% 1.42/0.57  % (13146)------------------------------
% 1.42/0.57  % (13134)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.70/0.57  fof(f8,axiom,(
% 1.70/0.57    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 1.70/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).
% 1.70/0.57  fof(f43,plain,(
% 1.70/0.57    v11_lattices(sK0)),
% 1.70/0.57    inference(cnf_transformation,[],[f35])).
% 1.70/0.57  fof(f274,plain,(
% 1.70/0.57    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))),
% 1.70/0.57    inference(forward_demodulation,[],[f273,f209])).
% 1.70/0.57  fof(f209,plain,(
% 1.70/0.57    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1)),
% 1.70/0.57    inference(forward_demodulation,[],[f206,f49])).
% 1.70/0.57  fof(f49,plain,(
% 1.70/0.57    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 1.70/0.57    inference(cnf_transformation,[],[f35])).
% 1.70/0.57  fof(f206,plain,(
% 1.70/0.57    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f45,f47,f65])).
% 1.70/0.57  fof(f273,plain,(
% 1.70/0.57    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))),
% 1.70/0.57    inference(forward_demodulation,[],[f153,f207])).
% 1.70/0.57  fof(f207,plain,(
% 1.70/0.57    k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f47,f65])).
% 1.70/0.57  fof(f153,plain,(
% 1.70/0.57    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2))),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f46,f45,f47,f57])).
% 1.70/0.57  fof(f1069,plain,(
% 1.70/0.57    k3_lattices(sK0,sK3,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f47,f124,f65])).
% 1.70/0.57  fof(f124,plain,(
% 1.70/0.57    m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.70/0.57    inference(forward_demodulation,[],[f107,f111])).
% 1.70/0.57  fof(f107,plain,(
% 1.70/0.57    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f73,f70,f45,f46,f62])).
% 1.70/0.57  fof(f62,plain,(
% 1.70/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.70/0.57    inference(cnf_transformation,[],[f24])).
% 1.70/0.57  fof(f24,plain,(
% 1.70/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.70/0.57    inference(flattening,[],[f23])).
% 1.70/0.57  fof(f23,plain,(
% 1.70/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.70/0.57    inference(ennf_transformation,[],[f4])).
% 1.70/0.57  fof(f4,axiom,(
% 1.70/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.70/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 1.70/0.57  fof(f1051,plain,(
% 1.70/0.57    k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f47,f124,f64])).
% 1.70/0.57  fof(f64,plain,(
% 1.70/0.57    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.70/0.57    inference(cnf_transformation,[],[f28])).
% 1.70/0.57  fof(f28,plain,(
% 1.70/0.57    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.70/0.57    inference(flattening,[],[f27])).
% 1.70/0.57  fof(f27,plain,(
% 1.70/0.57    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.70/0.57    inference(ennf_transformation,[],[f6])).
% 1.70/0.57  fof(f6,axiom,(
% 1.70/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 1.70/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 1.70/0.57  fof(f1068,plain,(
% 1.70/0.57    k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f124,f65])).
% 1.70/0.57  fof(f1050,plain,(
% 1.70/0.57    k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 1.70/0.57    inference(unit_resulting_resolution,[],[f41,f72,f71,f46,f124,f64])).
% 1.70/0.57  % SZS output end Proof for theBenchmark
% 1.70/0.57  % (13141)------------------------------
% 1.70/0.57  % (13141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.57  % (13141)Termination reason: Refutation
% 1.70/0.57  
% 1.70/0.57  % (13141)Memory used [KB]: 6908
% 1.70/0.57  % (13141)Time elapsed: 0.074 s
% 1.70/0.57  % (13141)------------------------------
% 1.70/0.57  % (13141)------------------------------
% 1.70/0.57  % (13125)Success in time 0.206 s
%------------------------------------------------------------------------------
