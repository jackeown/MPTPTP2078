%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (2476 expanded)
%              Number of leaves         :   18 (1094 expanded)
%              Depth                    :   17
%              Number of atoms          :  479 (22795 expanded)
%              Number of equality atoms :  135 (8079 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(global_subsumption,[],[f55,f312])).

fof(f312,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f231,f306])).

fof(f306,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(backward_demodulation,[],[f296,f171])).

fof(f171,plain,(
    sK3 = k4_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f79,f80,f81,f49,f52,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f33,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

fof(f49,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

% (32634)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
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

fof(f47,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f296,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(backward_demodulation,[],[f249,f295])).

fof(f295,plain,(
    sK2 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f251,f294])).

fof(f294,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f293,f167])).

fof(f167,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f162,f136])).

fof(f136,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f119,f127])).

fof(f127,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
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
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f119,plain,(
    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f46,f49,f80,f50,f51,f69])).

fof(f69,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f162,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f143,f104])).

fof(f104,plain,(
    sK2 = k4_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f79,f80,f81,f49,f51,f63])).

fof(f143,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f142,f133])).

fof(f133,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f125,f131])).

fof(f131,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f125,plain,(
    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f74])).

fof(f142,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f114,f128])).

fof(f128,plain,(
    k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f51,f74])).

fof(f114,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f51,f64])).

fof(f64,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,(
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
                ( k2_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),k2_lattices(X0,sK4(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),k2_lattices(X0,sK4(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f48,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f293,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f292,f228])).

fof(f228,plain,(
    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f208,f134])).

fof(f134,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f54,f123])).

fof(f123,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f78,f77,f50,f51,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f77,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f208,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f78,f77,f50,f52,f73])).

fof(f292,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f291,f133])).

fof(f291,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f173,f215])).

fof(f215,plain,(
    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f74])).

fof(f173,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f52,f64])).

fof(f251,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f250,f227])).

fof(f227,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f211,f223])).

fof(f223,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f220,f53])).

fof(f53,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f220,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f75])).

fof(f211,plain,(
    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f74])).

fof(f250,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f191,f226])).

fof(f226,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f212,f221])).

fof(f221,plain,(
    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f75])).

fof(f212,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f74])).

fof(f191,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f52,f64])).

fof(f249,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f248,f228])).

fof(f248,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f247,f227])).

fof(f247,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f192,f216])).

fof(f216,plain,(
    k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f52,f52,f74])).

fof(f192,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f48,f52,f50,f52,f64])).

fof(f231,plain,(
    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f202,f225])).

fof(f225,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f214,f53])).

fof(f214,plain,(
    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f74])).

fof(f202,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f46,f49,f80,f50,f52,f69])).

fof(f55,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (32637)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (32640)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (32639)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (32651)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (32645)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (32647)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (32636)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (32645)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f55,f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    sK2 = sK3),
% 0.21/0.49    inference(backward_demodulation,[],[f231,f306])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f296,f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    sK3 = k4_lattices(sK0,sK3,sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f79,f80,f81,f49,f52,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,X1,X1) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f33,f32,f31,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v9_lattices(sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f47,f49,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  % (32634)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v10_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v8_lattices(sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f47,f49,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v6_lattices(sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f47,f49,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f249,f295])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    sK2 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f251,f294])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f293,f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f162,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f119,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    l1_lattices(sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f49,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f49,f80,f50,f51,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0] : (((v8_lattices(X0) | ((sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f42,f44,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f143,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    sK2 = k4_lattices(sK0,sK2,sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f79,f80,f81,f49,f51,f63])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f142,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f51,f74])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f114,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f51,f74])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f51,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),k2_lattices(X0,sK4(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),k2_lattices(X0,sK4(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (? [X3] : (k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),k2_lattices(X0,sK4(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v11_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f292,f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f208,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f54,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f78,f77,f50,f51,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    l2_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f49,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v4_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f47,f49,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f78,f77,f50,f52,f73])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f291,f133])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f173,f215])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f74])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f52,f64])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f250,f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f211,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f220,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f75])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f74])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK2,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f191,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f212,f221])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f75])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f51,f52,f74])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f51,f50,f52,f64])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f248,f228])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f247,f227])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f192,f216])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f52,f52,f74])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f48,f52,f50,f52,f64])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f202,f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f214,f53])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f79,f76,f50,f52,f74])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f49,f80,f50,f52,f69])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    sK2 != sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (32645)------------------------------
% 0.21/0.50  % (32645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32645)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (32645)Memory used [KB]: 10874
% 0.21/0.50  % (32645)Time elapsed: 0.085 s
% 0.21/0.50  % (32645)------------------------------
% 0.21/0.50  % (32645)------------------------------
% 0.21/0.50  % (32629)Success in time 0.141 s
%------------------------------------------------------------------------------
