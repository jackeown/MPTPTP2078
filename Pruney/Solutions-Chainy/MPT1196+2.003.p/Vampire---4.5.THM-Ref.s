%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 109 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 ( 696 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(subsumption_resolution,[],[f179,f146])).

fof(f146,plain,(
    m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f89,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

fof(f89,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f88,f61])).

fof(f61,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f24,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X5] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f67,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f16,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f16,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f179,plain,(
    ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f135,f174])).

fof(f174,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(resolution,[],[f95,f18])).

fof(f95,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7 ) ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f23,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f24])).

fof(f93,plain,(
    ! [X7] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f69,f19])).

fof(f69,plain,(
    ! [X7] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7
      | ~ v9_lattices(sK0) ) ),
    inference(resolution,[],[f16,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f135,plain,
    ( ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f134,f18])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f133,f24])).

fof(f133,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f132,f23])).

fof(f132,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f131,f22])).

fof(f22,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f131,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f130,f19])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f17,plain,(
    ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (16648)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (16648)Refutation not found, incomplete strategy% (16648)------------------------------
% 0.20/0.47  % (16648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16648)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.48  % (16648)Memory used [KB]: 6140
% 0.20/0.48  % (16648)Time elapsed: 0.030 s
% 0.20/0.48  % (16648)------------------------------
% 0.20/0.48  % (16648)------------------------------
% 0.20/0.51  % (16662)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (16662)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f179,f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f89,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    l2_lattices(sK0)),
% 0.20/0.51    inference(resolution,[],[f24,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    l3_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X5] : (~l2_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f67,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X5] : (v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | m1_subset_1(k1_lattices(sK0,X5,sK2),u1_struct_0(sK0))) )),
% 0.20/0.51    inference(resolution,[],[f16,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    sK1 != sK1 | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.51    inference(backward_demodulation,[],[f135,f174])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(resolution,[],[f95,f18])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v9_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7 | ~v9_lattices(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f24])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X7] : (~l3_lattices(sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7 | ~v9_lattices(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f19])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X7] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,sK2)) = X7 | ~v9_lattices(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f16,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~v9_lattices(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f134,f18])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f24])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f132,f23])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f131,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v8_lattices(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f130,f19])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(resolution,[],[f17,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (16662)------------------------------
% 0.20/0.51  % (16662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16662)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (16662)Memory used [KB]: 1663
% 0.20/0.51  % (16662)Time elapsed: 0.081 s
% 0.20/0.51  % (16662)------------------------------
% 0.20/0.51  % (16662)------------------------------
% 0.20/0.52  % (16640)Success in time 0.163 s
%------------------------------------------------------------------------------
