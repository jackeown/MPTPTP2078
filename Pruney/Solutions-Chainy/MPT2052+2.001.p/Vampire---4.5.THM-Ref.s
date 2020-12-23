%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 597 expanded)
%              Number of leaves         :    3 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          :  225 (3244 expanded)
%              Number of equality atoms :   19 ( 118 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f57])).

fof(f57,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f55,f50])).

fof(f50,plain,(
    r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(forward_demodulation,[],[f48,f27])).

fof(f27,plain,(
    k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1) ),
    inference(subsumption_resolution,[],[f26,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r2_hidden(X2,k2_yellow19(X0,X1))
              <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

fof(f26,plain,
    ( v2_struct_0(sK0)
    | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1) ),
    inference(subsumption_resolution,[],[f25,f14])).

fof(f14,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1) ),
    inference(subsumption_resolution,[],[f24,f17])).

fof(f17,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1) ),
    inference(resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_yellow19)).

fof(f15,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f48,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f47,f13])).

fof(f13,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f46,f16])).

fof(f46,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f45,f15])).

fof(f45,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f44,f14])).

fof(f44,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f43,f17])).

fof(f43,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1)) ),
    inference(resolution,[],[f12,f23])).

fof(f23,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_waybel_0(X1,X2,X3)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | r2_hidden(X3,a_2_1_yellow19(X1,X2)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | ~ r1_waybel_0(X1,X2,X3)
      | r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).

fof(f12,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(resolution,[],[f54,f11])).

fof(f11,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f53,f51])).

fof(f51,plain,(
    sK2 = sK3(sK2,sK0,sK1) ),
    inference(resolution,[],[f38,f50])).

fof(f38,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | sK3(X1,sK0,sK1) = X1 ) ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f37,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | sK3(X1,sK0,sK1) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f36,f15])).

fof(f36,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | sK3(X1,sK0,sK1) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f35,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | sK3(X1,sK0,sK1) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f29,f17])).

fof(f29,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | sK3(X1,sK0,sK1) = X1
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f19,f27])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    r1_waybel_0(sK0,sK1,sK3(sK2,sK0,sK1)) ),
    inference(resolution,[],[f42,f50])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_yellow19(sK0,sK1))
      | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f41,f16])).

fof(f41,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_yellow19(sK0,sK1))
      | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f40,f15])).

fof(f40,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_yellow19(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f39,f14])).

fof(f39,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_yellow19(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f30,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_yellow19(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f20,f27])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | r1_waybel_0(X1,X2,sK3(X0,X1,X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f58,f51])).

fof(f58,plain,(
    m1_subset_1(sK3(sK2,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f34,f50])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_yellow19(sK0,sK1))
      | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_yellow19(sK0,sK1))
      | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_yellow19(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f31,f14])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_yellow19(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_yellow19(sK0,sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f18,f27])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n006.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:40:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.22/0.49  % (15744)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (15753)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15742)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (15740)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (15744)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (15763)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (15748)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (15760)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f59,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f55,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f48,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f26,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <~> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <~> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <=> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <=> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f25,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    v2_struct_0(sK1) | v2_struct_0(sK0) | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f24,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    l1_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | k2_yellow19(sK0,sK1) = a_2_1_yellow19(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f15,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_yellow19)).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    l1_waybel_0(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f47,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f46,f16])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f45,f15])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f44,f14])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f43,f17])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_yellow19(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_1_yellow19(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f12,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X2,X3,X1] : (~r1_waybel_0(X1,X2,X3) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | r2_hidden(X3,a_2_1_yellow19(X1,X2))) )),
% 0.22/0.51    inference(equality_resolution,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | X0 != X3 | ~r1_waybel_0(X1,X2,X3) | r2_hidden(X0,a_2_1_yellow19(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    r1_waybel_0(sK0,sK1,sK2) | r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f54,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ~r1_waybel_0(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,k2_yellow19(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    r1_waybel_0(sK0,sK1,sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f53,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    sK2 = sK3(sK2,sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f38,f50])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k2_yellow19(sK0,sK1)) | sK3(X1,sK0,sK1) = X1) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f37,f16])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k2_yellow19(sK0,sK1)) | sK3(X1,sK0,sK1) = X1 | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f36,f15])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k2_yellow19(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | sK3(X1,sK0,sK1) = X1 | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f35,f14])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k2_yellow19(sK0,sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | sK3(X1,sK0,sK1) = X1 | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f29,f17])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k2_yellow19(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | sK3(X1,sK0,sK1) = X1 | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(superposition,[],[f19,f27])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | sK3(X0,X1,X2) = X0 | v2_struct_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r1_waybel_0(sK0,sK1,sK3(sK2,sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f42,f50])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k2_yellow19(sK0,sK1)) | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f41,f16])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k2_yellow19(sK0,sK1)) | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f40,f15])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k2_yellow19(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f39,f14])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k2_yellow19(sK0,sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f30,f17])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k2_yellow19(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | r1_waybel_0(sK0,sK1,sK3(X2,sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(superposition,[],[f20,f27])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | r1_waybel_0(X1,X2,sK3(X0,X1,X2)) | v2_struct_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f58,f51])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    m1_subset_1(sK3(sK2,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f34,f50])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_yellow19(sK0,sK1)) | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f33,f16])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_yellow19(sK0,sK1)) | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f32,f15])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_yellow19(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f31,f14])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_yellow19(sK0,sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f28,f17])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_yellow19(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | m1_subset_1(sK3(X0,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(superposition,[],[f18,f27])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15744)------------------------------
% 0.22/0.51  % (15744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15744)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15744)Memory used [KB]: 6140
% 0.22/0.51  % (15745)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (15744)Time elapsed: 0.096 s
% 0.22/0.51  % (15744)------------------------------
% 0.22/0.51  % (15744)------------------------------
% 0.22/0.51  % (15750)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (15738)Success in time 0.151 s
%------------------------------------------------------------------------------
