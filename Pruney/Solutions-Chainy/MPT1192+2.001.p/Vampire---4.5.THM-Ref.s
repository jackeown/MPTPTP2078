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
% DateTime   : Thu Dec  3 13:10:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 393 expanded)
%              Number of leaves         :   13 ( 122 expanded)
%              Depth                    :   21
%              Number of atoms          :  437 (2354 expanded)
%              Number of equality atoms :   94 ( 397 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f41,f393])).

fof(f393,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f274,f391])).

fof(f391,plain,(
    sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f390,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k1_lattices(sK0,sK1,sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_lattices(X0,X1,X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_lattices(sK0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( k1_lattices(sK0,X1,X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k1_lattices(sK0,sK1,sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f390,plain,
    ( v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f380,f81])).

fof(f81,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f71,f35])).

fof(f71,plain,
    ( v2_struct_0(sK0)
    | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK1)) = X3
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

% (27162)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f380,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f369,f40])).

fof(f369,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f358,f40])).

fof(f358,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK1,k1_lattices(sK0,X5,X4)) = k4_lattices(sK0,sK1,k1_lattices(sK0,X5,X4))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f356,f40])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) = k4_lattices(sK0,X2,k1_lattices(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f276,f39])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X2,X1)) = k4_lattices(sK0,X0,k1_lattices(sK0,X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f120,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) = k4_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) = k4_lattices(sK0,X0,k1_lattices(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (27152)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f36])).

fof(f36,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f274,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)),sK1) ),
    inference(backward_demodulation,[],[f212,f273])).

fof(f273,plain,(
    k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f263,f35])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f252,f40])).

fof(f252,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f250,f40])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f186,f39])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f157,f43])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f137,f52])).

fof(f137,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,sK1) = k4_lattices(sK0,sK1,X3)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f40])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f109,f36])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f55])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f212,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) ),
    inference(backward_demodulation,[],[f183,f211])).

fof(f211,plain,(
    k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f201,f35])).

fof(f201,plain,
    ( v2_struct_0(sK0)
    | k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f190,f40])).

fof(f190,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f188,f40])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f185,f39])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f131,f43])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f52])).

fof(f111,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,sK1) = k4_lattices(sK0,X3,sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f40])).

fof(f183,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) ),
    inference(resolution,[],[f173,f35])).

fof(f173,plain,
    ( v2_struct_0(sK0)
    | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) ),
    inference(resolution,[],[f161,f40])).

fof(f161,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f159,f40])).

% (27152)Refutation not found, incomplete strategy% (27152)------------------------------
% (27152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27152)Termination reason: Refutation not found, incomplete strategy

% (27152)Memory used [KB]: 10618
% (27152)Time elapsed: 0.086 s
% (27152)------------------------------
% (27152)------------------------------
fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f158,f39])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f43])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1),sK1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1),sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f85,f52])).

fof(f85,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X3,sK1),sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f82,f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f41,plain,(
    sK1 != k1_lattices(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (27158)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.49  % (27163)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (27150)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (27158)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (27151)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (27171)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f412])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    sK1 != sK1),
% 0.22/0.50    inference(superposition,[],[f41,f393])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,sK1,sK1)),
% 0.22/0.50    inference(backward_demodulation,[],[f274,f391])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(resolution,[],[f390,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    (sK1 != k1_lattices(sK0,sK1,sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f23,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_lattices(sK0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X1] : (k1_lattices(sK0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k1_lattices(sK0,sK1,sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    v2_struct_0(sK0) | sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(forward_demodulation,[],[f380,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(resolution,[],[f71,f35])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    v2_struct_0(sK0) | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(resolution,[],[f60,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK1)) = X3 | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f57,f40])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f56,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l3_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f44,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v9_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  % (27162)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (((v9_lattices(X0) | ((sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f369,f40])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f358,f40])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,k1_lattices(sK0,X5,X4)) = k4_lattices(sK0,sK1,k1_lattices(sK0,X5,X4)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f356,f40])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) = k4_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f276,f39])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X2,X1)) = k4_lattices(sK0,X0,k1_lattices(sK0,X2,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f120,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l2_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) = k4_lattices(sK0,X0,k1_lattices(sK0,X1,X2))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) = k4_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f108,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  % (27152)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f83,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v6_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f53,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    l1_lattices(sK0)),
% 0.22/0.50    inference(resolution,[],[f42,f39])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)),sK1)),
% 0.22/0.50    inference(backward_demodulation,[],[f212,f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(resolution,[],[f263,f35])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    v2_struct_0(sK0) | k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 0.22/0.50    inference(resolution,[],[f252,f40])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k4_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,X3)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f250,f40])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f186,f39])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f157,f43])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X0,X1))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f137,f52])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k4_lattices(sK0,X3,sK1) = k4_lattices(sK0,sK1,X3) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f135,f40])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f109,f36])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f54,f55])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1)),
% 0.22/0.50    inference(backward_demodulation,[],[f183,f211])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f201,f35])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    v2_struct_0(sK0) | k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f190,f40])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f188,f40])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f185,f39])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) = k4_lattices(sK0,k1_lattices(sK0,X1,X0),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f131,f43])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) = k4_lattices(sK0,k1_lattices(sK0,X0,X1),sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f111,f52])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,sK1) = k4_lattices(sK0,X3,sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f108,f40])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f173,f35])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    v2_struct_0(sK0) | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f161,f40])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,X3),sK1),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f159,f40])).
% 0.22/0.50  % (27152)Refutation not found, incomplete strategy% (27152)------------------------------
% 0.22/0.50  % (27152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27152)Memory used [KB]: 10618
% 0.22/0.50  % (27152)Time elapsed: 0.086 s
% 0.22/0.50  % (27152)------------------------------
% 0.22/0.50  % (27152)------------------------------
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f158,f39])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X1,X0),sK1),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f105,f43])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1),sK1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,X0,X1),sK1),sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f85,f52])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,X3,sK1),sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f82,f40])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f58,f39])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f48,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v8_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : (((v8_lattices(X0) | ((sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f33,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK5(X0) != k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    sK1 != k1_lattices(sK0,sK1,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27158)------------------------------
% 0.22/0.51  % (27158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27158)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27158)Memory used [KB]: 1791
% 0.22/0.51  % (27158)Time elapsed: 0.074 s
% 0.22/0.51  % (27158)------------------------------
% 0.22/0.51  % (27158)------------------------------
% 0.22/0.51  % (27157)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (27148)Success in time 0.14 s
%------------------------------------------------------------------------------
