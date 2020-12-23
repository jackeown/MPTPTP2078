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
% DateTime   : Thu Dec  3 13:10:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 787 expanded)
%              Number of leaves         :   10 ( 135 expanded)
%              Depth                    :   32
%              Number of atoms          :  667 (5808 expanded)
%              Number of equality atoms :   24 ( 904 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f955,plain,(
    $false ),
    inference(subsumption_resolution,[],[f954,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

% (29600)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

fof(f954,plain,(
    ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f945,f40])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f945,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f935,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 != X2
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f935,plain,(
    r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f926,f35])).

fof(f926,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f925,f814])).

fof(f814,plain,(
    ! [X1] :
      ( ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f813,f35])).

fof(f813,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1)
      | r2_orders_2(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f806,f239])).

fof(f239,plain,(
    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f238,f33])).

fof(f33,plain,(
    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f238,plain,
    ( m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1) ),
    inference(resolution,[],[f235,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f235,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_orders_2(sK0,sK3,sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f227,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f227,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f225,f35])).

fof(f225,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,sK3,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f117,f140])).

fof(f140,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f139,f34])).

fof(f34,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f139,plain,
    ( ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f138,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f39,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f137,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f38,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f136,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f135,f37])).

fof(f37,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f31,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f31,plain,(
    m2_orders_2(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X18,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,(
    ! [X17,X18] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X18,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,(
    ! [X17,X18] :
      ( ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X18,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f114,f37])).

fof(f114,plain,(
    ! [X17,X18] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X18,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,(
    ! [X17,X18] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X18,u1_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f806,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1)
      | r2_orders_2(sK0,sK1,X1) ) ),
    inference(resolution,[],[f804,f111])).

fof(f111,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK0,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X10,X11)
      | r2_orders_2(sK0,X9,X11) ) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f110,plain,(
    ! [X10,X11,X9] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X9,X10)
      | ~ r2_orders_2(sK0,X10,X11)
      | r2_orders_2(sK0,X9,X11) ) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,(
    ! [X10,X11,X9] :
      ( ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X9,X10)
      | ~ r2_orders_2(sK0,X10,X11)
      | r2_orders_2(sK0,X9,X11) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X3)
      | r2_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f804,plain,(
    r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(subsumption_resolution,[],[f803,f239])).

fof(f803,plain,
    ( ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(subsumption_resolution,[],[f802,f35])).

fof(f802,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(subsumption_resolution,[],[f801,f40])).

fof(f801,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(subsumption_resolution,[],[f800,f37])).

fof(f800,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(subsumption_resolution,[],[f799,f36])).

fof(f799,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(resolution,[],[f790,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f790,plain,(
    r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1))) ),
    inference(resolution,[],[f787,f207])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r3_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f206,f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f140,f57])).

fof(f206,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f180,f31])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f179,f34])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f178,f35])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f177,f40])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f174,f37])).

fof(f174,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f172,f36])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f59,f32])).

fof(f32,plain,(
    sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X4,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X4,X0,X3)
      | ~ r2_hidden(X1,X4)
      | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X4,X0,X3)
      | ~ r2_hidden(X1,X4)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | r3_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

fof(f787,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3) ),
    inference(subsumption_resolution,[],[f786,f33])).

fof(f786,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3)
    | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1) ),
    inference(resolution,[],[f783,f51])).

fof(f783,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | r2_hidden(X2,sK3) ) ),
    inference(duplicate_literal_removal,[],[f765])).

fof(f765,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f762,f227])).

fof(f762,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X37,k3_orders_2(sK0,sK3,sK1))
      | ~ r2_hidden(X37,X38)
      | r2_hidden(X37,sK3) ) ),
    inference(resolution,[],[f554,f140])).

fof(f554,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k3_orders_2(sK0,X0,sK1))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f283,f35])).

fof(f283,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X8,X7)
      | ~ r2_hidden(X8,k3_orders_2(sK0,X7,X6))
      | ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f104,f57])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f925,plain,(
    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f924,f33])).

fof(f924,plain,
    ( r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1)
    | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1) ),
    inference(resolution,[],[f921,f51])).

fof(f921,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | r2_orders_2(sK0,X2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f903])).

fof(f903,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK1))
      | r2_orders_2(sK0,X2,sK1) ) ),
    inference(resolution,[],[f900,f227])).

fof(f900,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X37,k3_orders_2(sK0,sK3,sK1))
      | ~ r2_hidden(X37,X38)
      | r2_orders_2(sK0,X37,sK1) ) ),
    inference(resolution,[],[f629,f140])).

fof(f629,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X1,sK1)
      | ~ r2_hidden(X1,k3_orders_2(sK0,X0,sK1))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f352,f35])).

fof(f352,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X8,X6)
      | ~ r2_hidden(X8,k3_orders_2(sK0,X7,X6))
      | ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f100,f57])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (29602)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.46  % (29589)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (29589)Refutation not found, incomplete strategy% (29589)------------------------------
% 0.22/0.47  % (29589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29589)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29589)Memory used [KB]: 6140
% 0.22/0.47  % (29589)Time elapsed: 0.032 s
% 0.22/0.47  % (29589)------------------------------
% 0.22/0.47  % (29589)------------------------------
% 0.22/0.49  % (29607)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (29602)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f955,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f954,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % (29600)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).
% 0.22/0.49  fof(f954,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f945,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f945,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f935,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.22/0.49    inference(equality_resolution,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.49  fof(f935,plain,(
% 0.22/0.49    r2_orders_2(sK0,sK1,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f926,f35])).
% 0.22/0.49  fof(f926,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK1)),
% 0.22/0.49    inference(resolution,[],[f925,f814])).
% 0.22/0.49  fof(f814,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f813,f35])).
% 0.22/0.49  fof(f813,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1) | r2_orders_2(sK0,sK1,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f806,f239])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f238,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f235,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,k3_orders_2(sK0,sK3,sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f227,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f225,f35])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X5),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f117,f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f139,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f138,f40])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f136,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f135,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f133,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f31,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    m2_orders_2(sK3,sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f116,f40])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X17,X18] : (~l1_orders_2(sK0) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f38])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X17,X18] : (~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f114,f37])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X17,X18] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f95,f36])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ( ! [X17,X18] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X17,X18),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f39,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.22/0.49  fof(f806,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),X1) | r2_orders_2(sK0,sK1,X1)) )),
% 0.22/0.49    inference(resolution,[],[f804,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (~r1_orders_2(sK0,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X10,X11) | r2_orders_2(sK0,X9,X11)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f110,f40])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X9,X10) | ~r2_orders_2(sK0,X10,X11) | r2_orders_2(sK0,X9,X11)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f38])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X9,X10) | ~r2_orders_2(sK0,X10,X11) | r2_orders_2(sK0,X9,X11)) )),
% 0.22/0.49    inference(resolution,[],[f39,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X3) | r2_orders_2(X0,X1,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).
% 0.22/0.49  fof(f804,plain,(
% 0.22/0.49    r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f803,f239])).
% 0.22/0.49  fof(f803,plain,(
% 0.22/0.49    ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f802,f35])).
% 0.22/0.49  fof(f802,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f801,f40])).
% 0.22/0.49  fof(f801,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f800,f37])).
% 0.22/0.49  fof(f800,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f799,f36])).
% 0.22/0.49  fof(f799,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(resolution,[],[f790,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.49  fof(f790,plain,(
% 0.22/0.49    r3_orders_2(sK0,sK1,sK4(k3_orders_2(sK0,sK3,sK1)))),
% 0.22/0.49    inference(resolution,[],[f787,f207])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK3) | r3_orders_2(sK0,sK1,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f171])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK3) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f140,f57])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f180,f31])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f179,f34])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f178,f35])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f177,f40])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f176,f39])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f175,f38])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f174,f37])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f172,f36])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(superposition,[],[f59,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    sK1 = k1_funct_1(sK2,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X4,X0,X3) | ~r2_hidden(X1,X4) | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X4,X0,X3) | ~r2_hidden(X1,X4) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | r3_orders_2(X0,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).
% 0.22/0.49  fof(f787,plain,(
% 0.22/0.49    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f786,f33])).
% 0.22/0.49  fof(f786,plain,(
% 0.22/0.49    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1)),sK3) | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f783,f51])).
% 0.22/0.49  fof(f783,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | r2_hidden(X2,sK3)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f765])).
% 0.22/0.49  fof(f765,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | r2_hidden(X2,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f762,f227])).
% 0.22/0.49  fof(f762,plain,(
% 0.22/0.49    ( ! [X37,X38] : (~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X37,k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(X37,X38) | r2_hidden(X37,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f554,f140])).
% 0.22/0.49  fof(f554,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X0) | ~r2_hidden(X1,k3_orders_2(sK0,X0,sK1)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f283,f35])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X8,X7) | ~r2_hidden(X8,k3_orders_2(sK0,X7,X6)) | ~r2_hidden(X8,X9) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f104,f57])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f40])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f38])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f101,f37])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f36])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.22/0.49    inference(resolution,[],[f39,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.22/0.49  fof(f925,plain,(
% 0.22/0.49    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f924,f33])).
% 0.22/0.49  fof(f924,plain,(
% 0.22/0.49    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1)),sK1) | k1_xboole_0 = k3_orders_2(sK0,sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f921,f51])).
% 0.22/0.49  fof(f921,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | r2_orders_2(sK0,X2,sK1)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f903])).
% 0.22/0.49  fof(f903,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(X2,k3_orders_2(sK0,sK3,sK1)) | r2_orders_2(sK0,X2,sK1)) )),
% 0.22/0.49    inference(resolution,[],[f900,f227])).
% 0.22/0.49  fof(f900,plain,(
% 0.22/0.49    ( ! [X37,X38] : (~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X37,k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(X37,X38) | r2_orders_2(sK0,X37,sK1)) )),
% 0.22/0.49    inference(resolution,[],[f629,f140])).
% 0.22/0.49  fof(f629,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X1,sK1) | ~r2_hidden(X1,k3_orders_2(sK0,X0,sK1)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f352,f35])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X6) | ~r2_hidden(X8,k3_orders_2(sK0,X7,X6)) | ~r2_hidden(X8,X9) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(resolution,[],[f100,f57])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f40])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f98,f38])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f97,f37])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f36])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.49    inference(resolution,[],[f39,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (29602)------------------------------
% 0.22/0.49  % (29602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29602)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (29602)Memory used [KB]: 2174
% 0.22/0.49  % (29602)Time elapsed: 0.036 s
% 0.22/0.49  % (29602)------------------------------
% 0.22/0.49  % (29602)------------------------------
% 0.22/0.49  % (29588)Success in time 0.13 s
%------------------------------------------------------------------------------
