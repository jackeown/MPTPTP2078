%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:52 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 215 expanded)
%              Number of leaves         :    5 (  38 expanded)
%              Depth                    :   24
%              Number of atoms          :  271 (1460 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f37,plain,(
    sP5(sK0) ),
    inference(resolution,[],[f17,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f34_D])).

fof(f34_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f17,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(f90,plain,(
    ~ sP5(sK0) ),
    inference(subsumption_resolution,[],[f89,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,
    ( ~ l1_orders_2(sK0)
    | ~ sP5(sK0) ),
    inference(subsumption_resolution,[],[f88,f17])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ sP5(sK0) ),
    inference(resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f30,f34_D])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f87,plain,(
    r2_orders_2(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f86,f74])).

fof(f74,plain,(
    sK1 = sK3(sK1,sK0,sK2) ),
    inference(resolution,[],[f72,f16])).

fof(f16,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | sK3(X1,sK0,sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f71,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f14])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f69,f22])).

fof(f69,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f60,f19])).

fof(f19,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,sK2) = X1
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f29,f55])).

fof(f55,plain,(
    k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f54,f18])).

% (30102)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f54,plain,
    ( v2_struct_0(sK0)
    | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f53,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f40,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f86,plain,(
    r2_orders_2(sK0,sK1,sK3(sK1,sK0,sK2)) ),
    inference(resolution,[],[f83,f16])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f82,f19])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f18])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f17])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f14])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f21])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f20])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))
      | ~ v3_orders_2(sK0) ) ),
    inference(superposition,[],[f36,f55])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(X0,sK2))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_orders_2(X0,sK1,sK3(X1,X0,sK2))
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f15,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | v2_struct_0(X1)
      | r2_orders_2(X1,X4,sK3(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.45/0.55  % (30082)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.45/0.55  % (30092)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.56  % (30084)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.45/0.56  % (30083)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.45/0.56  % (30085)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.45/0.56  % (30080)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.45/0.56  % (30086)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.45/0.56  % (30085)Refutation not found, incomplete strategy% (30085)------------------------------
% 1.45/0.56  % (30085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30085)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (30083)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % (30085)Memory used [KB]: 1663
% 1.45/0.56  % (30085)Time elapsed: 0.126 s
% 1.45/0.56  % (30085)------------------------------
% 1.45/0.56  % (30085)------------------------------
% 1.45/0.56  % (30100)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.45/0.56  % (30098)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.58/0.56  % (30091)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.58/0.56  % SZS output start Proof for theBenchmark
% 1.58/0.56  fof(f91,plain,(
% 1.58/0.56    $false),
% 1.58/0.56    inference(subsumption_resolution,[],[f90,f37])).
% 1.58/0.56  fof(f37,plain,(
% 1.58/0.56    sP5(sK0)),
% 1.58/0.56    inference(resolution,[],[f17,f34])).
% 1.58/0.56  fof(f34,plain,(
% 1.58/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X0)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f34_D])).
% 1.58/0.56  fof(f34_D,plain,(
% 1.58/0.56    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,u1_struct_0(X0)) ) <=> ~sP5(X0)) )),
% 1.58/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.58/0.56  fof(f17,plain,(
% 1.58/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f7,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.58/0.56    inference(flattening,[],[f6])).
% 1.58/0.56  fof(f6,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.58/0.56    inference(ennf_transformation,[],[f5])).
% 1.58/0.56  fof(f5,negated_conjecture,(
% 1.58/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.58/0.56    inference(negated_conjecture,[],[f4])).
% 1.58/0.56  fof(f4,conjecture,(
% 1.58/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 1.58/0.56  fof(f90,plain,(
% 1.58/0.56    ~sP5(sK0)),
% 1.58/0.56    inference(subsumption_resolution,[],[f89,f22])).
% 1.58/0.56  fof(f22,plain,(
% 1.58/0.56    l1_orders_2(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f89,plain,(
% 1.58/0.56    ~l1_orders_2(sK0) | ~sP5(sK0)),
% 1.58/0.56    inference(subsumption_resolution,[],[f88,f17])).
% 1.58/0.56  fof(f88,plain,(
% 1.58/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~sP5(sK0)),
% 1.58/0.56    inference(resolution,[],[f87,f35])).
% 1.58/0.56  fof(f35,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~sP5(X0)) )),
% 1.58/0.56    inference(general_splitting,[],[f30,f34_D])).
% 1.58/0.56  fof(f30,plain,(
% 1.58/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X1)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f13])).
% 1.58/0.56  fof(f13,plain,(
% 1.58/0.56    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.58/0.56    inference(flattening,[],[f12])).
% 1.58/0.56  fof(f12,plain,(
% 1.58/0.56    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.58/0.56    inference(ennf_transformation,[],[f3])).
% 1.58/0.56  fof(f3,axiom,(
% 1.58/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => ~r2_orders_2(X0,X1,X1))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).
% 1.58/0.56  fof(f87,plain,(
% 1.58/0.56    r2_orders_2(sK0,sK1,sK1)),
% 1.58/0.56    inference(forward_demodulation,[],[f86,f74])).
% 1.58/0.56  fof(f74,plain,(
% 1.58/0.56    sK1 = sK3(sK1,sK0,sK2)),
% 1.58/0.56    inference(resolution,[],[f72,f16])).
% 1.58/0.56  fof(f16,plain,(
% 1.58/0.56    r2_hidden(sK1,k1_orders_2(sK0,sK2))),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f72,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | sK3(X1,sK0,sK2) = X1) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f71,f18])).
% 1.58/0.56  fof(f18,plain,(
% 1.58/0.56    ~v2_struct_0(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f71,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f70,f14])).
% 1.58/0.56  fof(f14,plain,(
% 1.58/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f70,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f69,f22])).
% 1.58/0.56  fof(f69,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f68,f21])).
% 1.58/0.56  fof(f21,plain,(
% 1.58/0.56    v5_orders_2(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f68,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f67,f20])).
% 1.58/0.56  fof(f20,plain,(
% 1.58/0.56    v4_orders_2(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f67,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(subsumption_resolution,[],[f60,f19])).
% 1.58/0.56  fof(f19,plain,(
% 1.58/0.56    v3_orders_2(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f60,plain,(
% 1.58/0.56    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,sK2) = X1 | v2_struct_0(sK0)) )),
% 1.58/0.56    inference(superposition,[],[f29,f55])).
% 1.58/0.56  fof(f55,plain,(
% 1.58/0.56    k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(subsumption_resolution,[],[f54,f18])).
% 1.58/0.56  % (30102)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.58/0.56  fof(f54,plain,(
% 1.58/0.56    v2_struct_0(sK0) | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(subsumption_resolution,[],[f53,f22])).
% 1.58/0.56  fof(f53,plain,(
% 1.58/0.56    ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(subsumption_resolution,[],[f52,f21])).
% 1.58/0.56  fof(f52,plain,(
% 1.58/0.56    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(subsumption_resolution,[],[f51,f20])).
% 1.58/0.56  fof(f51,plain,(
% 1.58/0.56    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(subsumption_resolution,[],[f40,f19])).
% 1.58/0.56  fof(f40,plain,(
% 1.58/0.56    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 1.58/0.56    inference(resolution,[],[f14,f23])).
% 1.58/0.56  fof(f23,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f9])).
% 1.58/0.56  fof(f9,plain,(
% 1.58/0.56    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/0.56    inference(flattening,[],[f8])).
% 1.58/0.56  fof(f8,plain,(
% 1.58/0.56    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/0.56    inference(ennf_transformation,[],[f1])).
% 1.58/0.56  fof(f1,axiom,(
% 1.58/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 1.58/0.56  fof(f29,plain,(
% 1.58/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK3(X0,X1,X2) = X0 | v2_struct_0(X1)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f11])).
% 1.58/0.56  fof(f11,plain,(
% 1.58/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.58/0.56    inference(flattening,[],[f10])).
% 1.58/0.56  fof(f10,plain,(
% 1.58/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.58/0.56    inference(ennf_transformation,[],[f2])).
% 1.58/0.56  fof(f2,axiom,(
% 1.58/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.58/0.56  fof(f86,plain,(
% 1.58/0.56    r2_orders_2(sK0,sK1,sK3(sK1,sK0,sK2))),
% 1.58/0.56    inference(resolution,[],[f83,f16])).
% 1.58/0.57  fof(f83,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2))) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f82,f19])).
% 1.58/0.57  fof(f82,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f81,f18])).
% 1.58/0.57  fof(f81,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f80,f17])).
% 1.58/0.57  fof(f80,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f79,f14])).
% 1.58/0.57  fof(f79,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f78,f22])).
% 1.58/0.57  fof(f78,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f77,f21])).
% 1.58/0.57  fof(f77,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f76,f20])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_orders_2(sK0,sK1,sK3(X0,sK0,sK2)) | ~v3_orders_2(sK0)) )),
% 1.58/0.57    inference(superposition,[],[f36,f55])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r2_hidden(X1,a_2_0_orders_2(X0,sK2)) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_orders_2(X0,sK1,sK3(X1,X0,sK2)) | ~v3_orders_2(X0)) )),
% 1.58/0.57    inference(resolution,[],[f15,f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | v2_struct_0(X1) | r2_orders_2(X1,X4,sK3(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    r2_hidden(sK1,sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f7])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (30083)------------------------------
% 1.58/0.57  % (30083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (30083)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (30083)Memory used [KB]: 6140
% 1.58/0.57  % (30083)Time elapsed: 0.129 s
% 1.58/0.57  % (30083)------------------------------
% 1.58/0.57  % (30083)------------------------------
% 1.58/0.57  % (30090)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.58/0.57  % (30077)Success in time 0.199 s
%------------------------------------------------------------------------------
