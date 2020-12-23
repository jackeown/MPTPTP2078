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
% DateTime   : Thu Dec  3 13:09:57 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 451 expanded)
%              Number of leaves         :   12 ( 172 expanded)
%              Depth                    :   18
%              Number of atoms          :  492 (3681 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f40])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,sK2))
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_hidden(X1,k2_orders_2(X0,X2))
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(sK0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( r2_hidden(X1,k2_orders_2(sK0,X2))
            & r2_hidden(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( r2_hidden(sK1,k2_orders_2(sK0,X2))
          & r2_hidden(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( r2_hidden(sK1,k2_orders_2(sK0,X2))
        & r2_hidden(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,k2_orders_2(sK0,sK2))
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
               => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(f227,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f226,f176])).

fof(f176,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f175,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f148,f65])).

fof(f65,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,sK1) ) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X1) ) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f58,f34])).

fof(f34,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X0) ) ),
    inference(resolution,[],[f134,f114])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK1,X2) ) ),
    inference(resolution,[],[f64,f38])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X1,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f134,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X2,sK1) ) ),
    inference(resolution,[],[f74,f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f37])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f226,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(forward_demodulation,[],[f225,f169])).

fof(f169,plain,(
    sK1 = sK4(sK1,sK0,sK2) ),
    inference(resolution,[],[f166,f41])).

fof(f41,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
      | sK4(X0,sK0,sK2) = X0 ) ),
    inference(forward_demodulation,[],[f165,f94])).

fof(f94,plain,(
    k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2) ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f68,f35])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f67,f36])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,sK2))
      | sK4(X0,sK0,sK2) = X0 ) ),
    inference(resolution,[],[f84,f39])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | sK4(X0,sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK4(X0,X1,X2) = X0
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_orders_2(sK0,sK4(sK1,sK0,sK2),X0) ) ),
    inference(resolution,[],[f171,f41])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
      | ~ r2_hidden(X1,sK2)
      | r2_orders_2(sK0,sK4(X0,sK0,sK2),X1) ) ),
    inference(forward_demodulation,[],[f170,f94])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,sK2))
      | ~ r2_hidden(X1,sK2)
      | r2_orders_2(sK0,sK4(X0,sK0,sK2),X1) ) ),
    inference(resolution,[],[f132,f39])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ r2_hidden(X0,X1)
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f130,f33])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f34])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f36])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(X1,sK4(X0,X1,X2),X6)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (803700737)
% 0.14/0.36  ipcrm: permission denied for id (807370754)
% 0.14/0.36  ipcrm: permission denied for id (802422787)
% 0.14/0.37  ipcrm: permission denied for id (803831814)
% 0.14/0.37  ipcrm: permission denied for id (803897352)
% 0.14/0.37  ipcrm: permission denied for id (807501833)
% 0.14/0.37  ipcrm: permission denied for id (802455562)
% 0.14/0.37  ipcrm: permission denied for id (803962891)
% 0.14/0.37  ipcrm: permission denied for id (803995660)
% 0.14/0.38  ipcrm: permission denied for id (807534605)
% 0.14/0.38  ipcrm: permission denied for id (804061198)
% 0.14/0.38  ipcrm: permission denied for id (804126736)
% 0.14/0.38  ipcrm: permission denied for id (802553876)
% 0.14/0.39  ipcrm: permission denied for id (807698453)
% 0.14/0.39  ipcrm: permission denied for id (807731222)
% 0.14/0.39  ipcrm: permission denied for id (804356119)
% 0.14/0.39  ipcrm: permission denied for id (807763992)
% 0.14/0.39  ipcrm: permission denied for id (804454426)
% 0.14/0.39  ipcrm: permission denied for id (807829531)
% 0.14/0.39  ipcrm: permission denied for id (802619420)
% 0.14/0.40  ipcrm: permission denied for id (802652189)
% 0.14/0.40  ipcrm: permission denied for id (804519966)
% 0.14/0.40  ipcrm: permission denied for id (807927841)
% 0.14/0.40  ipcrm: permission denied for id (804651042)
% 0.14/0.40  ipcrm: permission denied for id (807960611)
% 0.14/0.40  ipcrm: permission denied for id (807993380)
% 0.21/0.40  ipcrm: permission denied for id (808026149)
% 0.21/0.41  ipcrm: permission denied for id (808058918)
% 0.21/0.41  ipcrm: permission denied for id (804814887)
% 0.21/0.41  ipcrm: permission denied for id (802750504)
% 0.21/0.41  ipcrm: permission denied for id (808157226)
% 0.21/0.41  ipcrm: permission denied for id (804945964)
% 0.21/0.41  ipcrm: permission denied for id (808222765)
% 0.21/0.42  ipcrm: permission denied for id (802848815)
% 0.21/0.42  ipcrm: permission denied for id (805044272)
% 0.21/0.42  ipcrm: permission denied for id (805077041)
% 0.21/0.42  ipcrm: permission denied for id (802881587)
% 0.21/0.42  ipcrm: permission denied for id (805142580)
% 0.21/0.42  ipcrm: permission denied for id (805175349)
% 0.21/0.43  ipcrm: permission denied for id (805208118)
% 0.21/0.43  ipcrm: permission denied for id (805273656)
% 0.21/0.43  ipcrm: permission denied for id (805306425)
% 0.21/0.43  ipcrm: permission denied for id (805339194)
% 0.21/0.43  ipcrm: permission denied for id (805404732)
% 0.21/0.43  ipcrm: permission denied for id (802979901)
% 0.21/0.44  ipcrm: permission denied for id (805470271)
% 0.21/0.44  ipcrm: permission denied for id (803045440)
% 0.21/0.44  ipcrm: permission denied for id (803078213)
% 0.21/0.44  ipcrm: permission denied for id (808583239)
% 0.21/0.45  ipcrm: permission denied for id (808648777)
% 0.21/0.45  ipcrm: permission denied for id (808681546)
% 0.21/0.45  ipcrm: permission denied for id (808714315)
% 0.21/0.45  ipcrm: permission denied for id (803143756)
% 0.21/0.45  ipcrm: permission denied for id (805863502)
% 0.21/0.46  ipcrm: permission denied for id (805929040)
% 0.21/0.46  ipcrm: permission denied for id (808812625)
% 0.21/0.46  ipcrm: permission denied for id (808845394)
% 0.21/0.46  ipcrm: permission denied for id (806027347)
% 0.21/0.46  ipcrm: permission denied for id (808878164)
% 0.21/0.46  ipcrm: permission denied for id (806092885)
% 0.21/0.46  ipcrm: permission denied for id (806125654)
% 0.21/0.46  ipcrm: permission denied for id (806158423)
% 0.21/0.46  ipcrm: permission denied for id (806191192)
% 0.21/0.47  ipcrm: permission denied for id (808943706)
% 0.21/0.47  ipcrm: permission denied for id (806289499)
% 0.21/0.47  ipcrm: permission denied for id (803209309)
% 0.21/0.47  ipcrm: permission denied for id (806355038)
% 0.21/0.47  ipcrm: permission denied for id (806387807)
% 0.21/0.47  ipcrm: permission denied for id (809009248)
% 0.21/0.48  ipcrm: permission denied for id (809042017)
% 0.21/0.48  ipcrm: permission denied for id (803274850)
% 0.21/0.48  ipcrm: permission denied for id (806486115)
% 0.21/0.48  ipcrm: permission denied for id (809074788)
% 0.21/0.48  ipcrm: permission denied for id (803307622)
% 0.21/0.48  ipcrm: permission denied for id (806584423)
% 0.21/0.48  ipcrm: permission denied for id (803340392)
% 0.21/0.49  ipcrm: permission denied for id (806649962)
% 0.21/0.49  ipcrm: permission denied for id (806715500)
% 0.21/0.49  ipcrm: permission denied for id (806748269)
% 0.21/0.49  ipcrm: permission denied for id (806781038)
% 0.21/0.49  ipcrm: permission denied for id (806879344)
% 0.21/0.49  ipcrm: permission denied for id (803471473)
% 0.21/0.50  ipcrm: permission denied for id (809238642)
% 0.21/0.50  ipcrm: permission denied for id (803569780)
% 0.21/0.50  ipcrm: permission denied for id (807010422)
% 0.21/0.51  ipcrm: permission denied for id (809435258)
% 0.21/0.51  ipcrm: permission denied for id (809500796)
% 0.21/0.51  ipcrm: permission denied for id (807239805)
% 0.21/0.51  ipcrm: permission denied for id (809533566)
% 0.21/0.51  ipcrm: permission denied for id (809566335)
% 0.94/0.62  % (20814)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.94/0.62  % (20822)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.94/0.63  % (20822)Refutation found. Thanks to Tanya!
% 0.94/0.63  % SZS status Theorem for theBenchmark
% 0.94/0.63  % SZS output start Proof for theBenchmark
% 0.94/0.63  fof(f228,plain,(
% 0.94/0.63    $false),
% 0.94/0.63    inference(subsumption_resolution,[],[f227,f40])).
% 0.94/0.63  fof(f40,plain,(
% 0.94/0.63    r2_hidden(sK1,sK2)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f26,plain,(
% 0.94/0.63    ((r2_hidden(sK1,k2_orders_2(sK0,sK2)) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.94/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f25,f24,f23])).
% 0.94/0.63  fof(f23,plain,(
% 0.94/0.63    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.94/0.63    introduced(choice_axiom,[])).
% 0.94/0.63  fof(f24,plain,(
% 0.94/0.63    ? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (r2_hidden(sK1,k2_orders_2(sK0,X2)) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.94/0.63    introduced(choice_axiom,[])).
% 0.94/0.63  fof(f25,plain,(
% 0.94/0.63    ? [X2] : (r2_hidden(sK1,k2_orders_2(sK0,X2)) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,k2_orders_2(sK0,sK2)) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.94/0.63    introduced(choice_axiom,[])).
% 0.94/0.63  fof(f10,plain,(
% 0.94/0.63    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.94/0.63    inference(flattening,[],[f9])).
% 0.94/0.63  fof(f9,plain,(
% 0.94/0.63    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.94/0.63    inference(ennf_transformation,[],[f8])).
% 0.94/0.63  fof(f8,negated_conjecture,(
% 0.94/0.63    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.94/0.63    inference(negated_conjecture,[],[f7])).
% 0.94/0.63  fof(f7,conjecture,(
% 0.94/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 0.94/0.63  fof(f227,plain,(
% 0.94/0.63    ~r2_hidden(sK1,sK2)),
% 0.94/0.63    inference(resolution,[],[f226,f176])).
% 0.94/0.63  fof(f176,plain,(
% 0.94/0.63    ~r2_orders_2(sK0,sK1,sK1)),
% 0.94/0.63    inference(subsumption_resolution,[],[f175,f38])).
% 0.94/0.63  fof(f38,plain,(
% 0.94/0.63    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f175,plain,(
% 0.94/0.63    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,sK1)),
% 0.94/0.63    inference(resolution,[],[f148,f65])).
% 0.94/0.63  fof(f65,plain,(
% 0.94/0.63    r3_orders_2(sK0,sK1,sK1)),
% 0.94/0.63    inference(resolution,[],[f61,f38])).
% 0.94/0.63  fof(f61,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)) )),
% 0.94/0.63    inference(resolution,[],[f60,f38])).
% 0.94/0.63  fof(f60,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X1)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f59,f33])).
% 0.94/0.63  fof(f33,plain,(
% 0.94/0.63    ~v2_struct_0(sK0)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f59,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X1) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f58,f34])).
% 0.94/0.63  fof(f34,plain,(
% 0.94/0.63    v3_orders_2(sK0)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f58,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f50,f37])).
% 0.94/0.63  fof(f37,plain,(
% 0.94/0.63    l1_orders_2(sK0)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f50,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f18])).
% 0.94/0.63  fof(f18,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.94/0.63    inference(flattening,[],[f17])).
% 0.94/0.63  fof(f17,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.94/0.63    inference(ennf_transformation,[],[f5])).
% 0.94/0.63  fof(f5,axiom,(
% 0.94/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.94/0.63  fof(f148,plain,(
% 0.94/0.63    ( ! [X0] : (~r3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0)) )),
% 0.94/0.63    inference(duplicate_literal_removal,[],[f147])).
% 0.94/0.63  fof(f147,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0)) )),
% 0.94/0.63    inference(resolution,[],[f134,f114])).
% 0.94/0.63  fof(f114,plain,(
% 0.94/0.63    ( ! [X2] : (~r1_orders_2(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X2)) )),
% 0.94/0.63    inference(resolution,[],[f64,f38])).
% 0.94/0.63  fof(f64,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X1,X0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f63,f36])).
% 0.94/0.63  fof(f36,plain,(
% 0.94/0.63    v5_orders_2(sK0)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f63,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X1,X0) | ~v5_orders_2(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f43,f37])).
% 0.94/0.63  fof(f43,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X1) | ~v5_orders_2(X0)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f14])).
% 0.94/0.63  fof(f14,plain,(
% 0.94/0.63    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.94/0.63    inference(flattening,[],[f13])).
% 0.94/0.63  fof(f13,plain,(
% 0.94/0.63    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.94/0.63    inference(ennf_transformation,[],[f6])).
% 0.94/0.63  fof(f6,axiom,(
% 0.94/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).
% 0.94/0.63  fof(f134,plain,(
% 0.94/0.63    ( ! [X2] : (r1_orders_2(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X2,sK1)) )),
% 0.94/0.63    inference(resolution,[],[f74,f38])).
% 0.94/0.63  fof(f74,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f73,f33])).
% 0.94/0.63  fof(f73,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f72,f34])).
% 0.94/0.63  fof(f72,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f51,f37])).
% 0.94/0.63  fof(f51,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f32])).
% 0.94/0.63  fof(f32,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.94/0.63    inference(nnf_transformation,[],[f20])).
% 0.94/0.63  fof(f20,plain,(
% 0.94/0.63    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.94/0.63    inference(flattening,[],[f19])).
% 0.94/0.63  fof(f19,plain,(
% 0.94/0.63    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.94/0.63    inference(ennf_transformation,[],[f4])).
% 0.94/0.63  fof(f4,axiom,(
% 0.94/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.94/0.63  fof(f226,plain,(
% 0.94/0.63    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,sK2)) )),
% 0.94/0.63    inference(forward_demodulation,[],[f225,f169])).
% 0.94/0.63  fof(f169,plain,(
% 0.94/0.63    sK1 = sK4(sK1,sK0,sK2)),
% 0.94/0.63    inference(resolution,[],[f166,f41])).
% 0.94/0.63  fof(f41,plain,(
% 0.94/0.63    r2_hidden(sK1,k2_orders_2(sK0,sK2))),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f166,plain,(
% 0.94/0.63    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,sK2)) | sK4(X0,sK0,sK2) = X0) )),
% 0.94/0.63    inference(forward_demodulation,[],[f165,f94])).
% 0.94/0.63  fof(f94,plain,(
% 0.94/0.63    k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)),
% 0.94/0.63    inference(resolution,[],[f71,f39])).
% 0.94/0.63  fof(f39,plain,(
% 0.94/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f71,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f70,f33])).
% 0.94/0.63  fof(f70,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f69,f34])).
% 0.94/0.63  fof(f69,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f68,f35])).
% 0.94/0.63  fof(f35,plain,(
% 0.94/0.63    v4_orders_2(sK0)),
% 0.94/0.63    inference(cnf_transformation,[],[f26])).
% 0.94/0.63  fof(f68,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f67,f36])).
% 0.94/0.63  fof(f67,plain,(
% 0.94/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f42,f37])).
% 0.94/0.63  fof(f42,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f12])).
% 0.94/0.63  fof(f12,plain,(
% 0.94/0.63    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.94/0.63    inference(flattening,[],[f11])).
% 0.94/0.63  fof(f11,plain,(
% 0.94/0.63    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.94/0.63    inference(ennf_transformation,[],[f2])).
% 0.94/0.63  fof(f2,axiom,(
% 0.94/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.94/0.63  fof(f165,plain,(
% 0.94/0.63    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,sK2)) | sK4(X0,sK0,sK2) = X0) )),
% 0.94/0.63    inference(resolution,[],[f84,f39])).
% 0.94/0.63  fof(f84,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK4(X0,sK0,X1) = X0) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f83,f33])).
% 0.94/0.63  fof(f83,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f82,f34])).
% 0.94/0.63  fof(f82,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f81,f35])).
% 0.94/0.63  fof(f81,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f80,f36])).
% 0.94/0.63  fof(f80,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f45,f37])).
% 0.94/0.63  fof(f45,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK4(X0,X1,X2) = X0 | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f31])).
% 0.94/0.63  fof(f31,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.94/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).
% 0.94/0.63  fof(f29,plain,(
% 0.94/0.63    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 0.94/0.63    introduced(choice_axiom,[])).
% 0.94/0.63  fof(f30,plain,(
% 0.94/0.63    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.94/0.63    introduced(choice_axiom,[])).
% 0.94/0.63  fof(f28,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.94/0.63    inference(rectify,[],[f27])).
% 0.94/0.63  fof(f27,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.94/0.63    inference(nnf_transformation,[],[f16])).
% 0.94/0.63  fof(f16,plain,(
% 0.94/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.94/0.63    inference(flattening,[],[f15])).
% 0.94/0.63  fof(f15,plain,(
% 0.94/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.94/0.63    inference(ennf_transformation,[],[f3])).
% 0.94/0.63  fof(f3,axiom,(
% 0.94/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.94/0.63  fof(f225,plain,(
% 0.94/0.63    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_orders_2(sK0,sK4(sK1,sK0,sK2),X0)) )),
% 0.94/0.63    inference(resolution,[],[f171,f41])).
% 0.94/0.63  fof(f171,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,sK2)) | ~r2_hidden(X1,sK2) | r2_orders_2(sK0,sK4(X0,sK0,sK2),X1)) )),
% 0.94/0.63    inference(forward_demodulation,[],[f170,f94])).
% 0.94/0.63  fof(f170,plain,(
% 0.94/0.63    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,sK2)) | ~r2_hidden(X1,sK2) | r2_orders_2(sK0,sK4(X0,sK0,sK2),X1)) )),
% 0.94/0.63    inference(resolution,[],[f132,f39])).
% 0.94/0.63  fof(f132,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~r2_hidden(X0,X1) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f131,f53])).
% 0.94/0.63  fof(f53,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f22])).
% 0.94/0.63  fof(f22,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.94/0.63    inference(flattening,[],[f21])).
% 0.94/0.63  fof(f21,plain,(
% 0.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.94/0.63    inference(ennf_transformation,[],[f1])).
% 0.94/0.63  fof(f1,axiom,(
% 0.94/0.63    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.94/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.94/0.63  fof(f131,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f130,f33])).
% 0.94/0.63  fof(f130,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f129,f34])).
% 0.94/0.63  fof(f129,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f128,f35])).
% 0.94/0.63  fof(f128,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(subsumption_resolution,[],[f127,f36])).
% 0.94/0.63  fof(f127,plain,(
% 0.94/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.94/0.63    inference(resolution,[],[f46,f37])).
% 0.94/0.63  fof(f46,plain,(
% 0.94/0.63    ( ! [X6,X2,X0,X1] : (~l1_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.94/0.63    inference(cnf_transformation,[],[f31])).
% 0.94/0.63  % SZS output end Proof for theBenchmark
% 0.94/0.63  % (20822)------------------------------
% 0.94/0.63  % (20822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.94/0.63  % (20822)Termination reason: Refutation
% 0.94/0.63  
% 0.94/0.63  % (20822)Memory used [KB]: 1663
% 0.94/0.63  % (20822)Time elapsed: 0.061 s
% 0.94/0.63  % (20822)------------------------------
% 0.94/0.63  % (20822)------------------------------
% 0.94/0.63  % (20672)Success in time 0.279 s
%------------------------------------------------------------------------------
