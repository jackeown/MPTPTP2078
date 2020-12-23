%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1855+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 52.93s
% Output     : Refutation 52.93s
% Verified   : 
% Statistics : Number of formulae       :  147 (1217 expanded)
%              Number of leaves         :   18 ( 374 expanded)
%              Depth                    :   22
%              Number of atoms          :  541 (7451 expanded)
%              Number of equality atoms :   93 (1029 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143797,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143770,f45923])).

fof(f45923,plain,(
    u1_struct_0(sK35) = u1_struct_0(k1_tex_2(sK34,sK53(sK35))) ),
    inference(backward_demodulation,[],[f43850,f45921])).

fof(f45921,plain,(
    u1_struct_0(sK35) = k1_tarski(sK53(sK35)) ),
    inference(forward_demodulation,[],[f45920,f7210])).

fof(f7210,plain,(
    u1_struct_0(sK35) = k6_domain_1(u1_struct_0(sK35),sK53(sK35)) ),
    inference(subsumption_resolution,[],[f7209,f4556])).

fof(f4556,plain,(
    ~ v2_struct_0(sK35) ),
    inference(cnf_transformation,[],[f4192])).

fof(f4192,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2))) != g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35))
        | ~ m1_subset_1(X2,u1_struct_0(sK34)) )
    & m1_pre_topc(sK35,sK34)
    & v7_struct_0(sK35)
    & ~ v2_struct_0(sK35)
    & l1_pre_topc(sK34)
    & ~ v2_struct_0(sK34) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34,sK35])],[f3638,f4191,f4190])).

fof(f4190,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK34)) )
          & m1_pre_topc(X1,sK34)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK34)
      & ~ v2_struct_0(sK34) ) ),
    introduced(choice_axiom,[])).

fof(f4191,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(sK34)) )
        & m1_pre_topc(X1,sK34)
        & v7_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2))) != g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35))
          | ~ m1_subset_1(X2,u1_struct_0(sK34)) )
      & m1_pre_topc(sK35,sK34)
      & v7_struct_0(sK35)
      & ~ v2_struct_0(sK35) ) ),
    introduced(choice_axiom,[])).

fof(f3638,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3637])).

fof(f3637,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3622])).

fof(f3622,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3621])).

fof(f3621,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

fof(f7209,plain,
    ( u1_struct_0(sK35) = k6_domain_1(u1_struct_0(sK35),sK53(sK35))
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f7171,f4557])).

fof(f4557,plain,(
    v7_struct_0(sK35) ),
    inference(cnf_transformation,[],[f4192])).

fof(f7171,plain,
    ( u1_struct_0(sK35) = k6_domain_1(u1_struct_0(sK35),sK53(sK35))
    | ~ v7_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6927,f4693])).

fof(f4693,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK53(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4245])).

fof(f4245,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK53(X0))
            & m1_subset_1(sK53(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK53])],[f4243,f4244])).

fof(f4244,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK53(X0))
        & m1_subset_1(sK53(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4243,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4242])).

fof(f4242,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3736])).

fof(f3736,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3735])).

fof(f3735,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3571])).

fof(f3571,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

fof(f6927,plain,(
    l1_struct_0(sK35) ),
    inference(resolution,[],[f6534,f4975])).

fof(f4975,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3946])).

fof(f3946,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f6534,plain,(
    l1_pre_topc(sK35) ),
    inference(subsumption_resolution,[],[f6392,f4555])).

fof(f4555,plain,(
    l1_pre_topc(sK34) ),
    inference(cnf_transformation,[],[f4192])).

fof(f6392,plain,
    ( l1_pre_topc(sK35)
    | ~ l1_pre_topc(sK34) ),
    inference(resolution,[],[f4558,f4629])).

fof(f4629,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3708])).

fof(f3708,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4558,plain,(
    m1_pre_topc(sK35,sK34) ),
    inference(cnf_transformation,[],[f4192])).

fof(f45920,plain,(
    k6_domain_1(u1_struct_0(sK35),sK53(sK35)) = k1_tarski(sK53(sK35)) ),
    inference(subsumption_resolution,[],[f45866,f7218])).

fof(f7218,plain,(
    ~ v1_xboole_0(u1_struct_0(sK35)) ),
    inference(subsumption_resolution,[],[f7195,f4556])).

fof(f7195,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK35))
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6927,f4974])).

fof(f4974,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3945])).

fof(f3945,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3944])).

fof(f3944,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f45866,plain,
    ( k6_domain_1(u1_struct_0(sK35),sK53(sK35)) = k1_tarski(sK53(sK35))
    | v1_xboole_0(u1_struct_0(sK35)) ),
    inference(resolution,[],[f7208,f4689])).

fof(f4689,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3732])).

fof(f3732,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3731])).

fof(f3731,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f7208,plain,(
    m1_subset_1(sK53(sK35),u1_struct_0(sK35)) ),
    inference(subsumption_resolution,[],[f7207,f4556])).

fof(f7207,plain,
    ( m1_subset_1(sK53(sK35),u1_struct_0(sK35))
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f7170,f4557])).

fof(f7170,plain,
    ( m1_subset_1(sK53(sK35),u1_struct_0(sK35))
    | ~ v7_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6927,f4692])).

fof(f4692,plain,(
    ! [X0] :
      ( m1_subset_1(sK53(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4245])).

fof(f43850,plain,(
    u1_struct_0(k1_tex_2(sK34,sK53(sK35))) = k1_tarski(sK53(sK35)) ),
    inference(backward_demodulation,[],[f43775,f43849])).

fof(f43849,plain,(
    k6_domain_1(u1_struct_0(sK34),sK53(sK35)) = k1_tarski(sK53(sK35)) ),
    inference(subsumption_resolution,[],[f43807,f6342])).

fof(f6342,plain,(
    ~ v1_xboole_0(u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f6308,f4554])).

fof(f4554,plain,(
    ~ v2_struct_0(sK34) ),
    inference(cnf_transformation,[],[f4192])).

fof(f6308,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK34))
    | v2_struct_0(sK34) ),
    inference(resolution,[],[f5911,f4974])).

fof(f5911,plain,(
    l1_struct_0(sK34) ),
    inference(resolution,[],[f4555,f4975])).

fof(f43807,plain,
    ( k6_domain_1(u1_struct_0(sK34),sK53(sK35)) = k1_tarski(sK53(sK35))
    | v1_xboole_0(u1_struct_0(sK34)) ),
    inference(resolution,[],[f27458,f4689])).

fof(f27458,plain,(
    m1_subset_1(sK53(sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f27457,f4556])).

fof(f27457,plain,
    ( m1_subset_1(sK53(sK35),u1_struct_0(sK34))
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f27456,f6927])).

fof(f27456,plain,
    ( m1_subset_1(sK53(sK35),u1_struct_0(sK34))
    | ~ l1_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f27431,f4557])).

fof(f27431,plain,
    ( m1_subset_1(sK53(sK35),u1_struct_0(sK34))
    | ~ v7_struct_0(sK35)
    | ~ l1_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6529,f4692])).

fof(f6529,plain,(
    ! [X29] :
      ( ~ m1_subset_1(X29,u1_struct_0(sK35))
      | m1_subset_1(X29,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f6528,f4554])).

fof(f6528,plain,(
    ! [X29] :
      ( m1_subset_1(X29,u1_struct_0(sK34))
      | ~ m1_subset_1(X29,u1_struct_0(sK35))
      | v2_struct_0(sK34) ) ),
    inference(subsumption_resolution,[],[f6527,f4555])).

fof(f6527,plain,(
    ! [X29] :
      ( m1_subset_1(X29,u1_struct_0(sK34))
      | ~ m1_subset_1(X29,u1_struct_0(sK35))
      | ~ l1_pre_topc(sK34)
      | v2_struct_0(sK34) ) ),
    inference(subsumption_resolution,[],[f6386,f4556])).

fof(f6386,plain,(
    ! [X29] :
      ( m1_subset_1(X29,u1_struct_0(sK34))
      | ~ m1_subset_1(X29,u1_struct_0(sK35))
      | v2_struct_0(sK35)
      | ~ l1_pre_topc(sK34)
      | v2_struct_0(sK34) ) ),
    inference(resolution,[],[f4558,f4622])).

fof(f4622,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3701])).

fof(f3701,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3700])).

fof(f3700,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1846])).

fof(f1846,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f43775,plain,(
    k6_domain_1(u1_struct_0(sK34),sK53(sK35)) = u1_struct_0(k1_tex_2(sK34,sK53(sK35))) ),
    inference(resolution,[],[f27458,f5725])).

fof(f5725,plain,(
    ! [X423] :
      ( ~ m1_subset_1(X423,u1_struct_0(sK34))
      | k6_domain_1(u1_struct_0(sK34),X423) = u1_struct_0(k1_tex_2(sK34,X423)) ) ),
    inference(subsumption_resolution,[],[f5724,f5610])).

fof(f5610,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK34))
      | ~ v2_struct_0(k1_tex_2(sK34,X0)) ) ),
    inference(subsumption_resolution,[],[f5400,f4555])).

fof(f5400,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_tex_2(sK34,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK34))
      | ~ l1_pre_topc(sK34) ) ),
    inference(resolution,[],[f4554,f4560])).

fof(f4560,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3640])).

fof(f3640,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3639])).

fof(f3639,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3578])).

fof(f3578,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f5724,plain,(
    ! [X423] :
      ( k6_domain_1(u1_struct_0(sK34),X423) = u1_struct_0(k1_tex_2(sK34,X423))
      | v2_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_subset_1(X423,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f5723,f5612])).

fof(f5612,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK34))
      | m1_pre_topc(k1_tex_2(sK34,X2),sK34) ) ),
    inference(subsumption_resolution,[],[f5402,f4555])).

fof(f5402,plain,(
    ! [X2] :
      ( m1_pre_topc(k1_tex_2(sK34,X2),sK34)
      | ~ m1_subset_1(X2,u1_struct_0(sK34))
      | ~ l1_pre_topc(sK34) ) ),
    inference(resolution,[],[f4554,f4562])).

fof(f4562,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3640])).

fof(f5723,plain,(
    ! [X423] :
      ( k6_domain_1(u1_struct_0(sK34),X423) = u1_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_pre_topc(k1_tex_2(sK34,X423),sK34)
      | v2_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_subset_1(X423,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f5722,f5611])).

fof(f5611,plain,(
    ! [X1] :
      ( v1_pre_topc(k1_tex_2(sK34,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f5401,f4555])).

fof(f5401,plain,(
    ! [X1] :
      ( v1_pre_topc(k1_tex_2(sK34,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK34))
      | ~ l1_pre_topc(sK34) ) ),
    inference(resolution,[],[f4554,f4561])).

fof(f4561,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3640])).

fof(f5722,plain,(
    ! [X423] :
      ( k6_domain_1(u1_struct_0(sK34),X423) = u1_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_pre_topc(k1_tex_2(sK34,X423),sK34)
      | ~ v1_pre_topc(k1_tex_2(sK34,X423))
      | v2_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_subset_1(X423,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f5598,f4555])).

fof(f5598,plain,(
    ! [X423] :
      ( k6_domain_1(u1_struct_0(sK34),X423) = u1_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_pre_topc(k1_tex_2(sK34,X423),sK34)
      | ~ v1_pre_topc(k1_tex_2(sK34,X423))
      | v2_struct_0(k1_tex_2(sK34,X423))
      | ~ m1_subset_1(X423,u1_struct_0(sK34))
      | ~ l1_pre_topc(sK34) ) ),
    inference(resolution,[],[f4554,f5335])).

fof(f5335,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4566])).

fof(f4566,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4193])).

fof(f4193,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3644])).

fof(f3644,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3643])).

fof(f3643,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3576])).

fof(f3576,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(f143770,plain,(
    u1_struct_0(sK35) != u1_struct_0(k1_tex_2(sK34,sK53(sK35))) ),
    inference(resolution,[],[f40500,f27458])).

fof(f40500,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,u1_struct_0(sK34))
      | u1_struct_0(sK35) != u1_struct_0(k1_tex_2(sK34,X22)) ) ),
    inference(subsumption_resolution,[],[f40499,f19243])).

fof(f19243,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK34))
      | g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2))) != sK45(sK35) ) ),
    inference(backward_demodulation,[],[f4559,f19242])).

fof(f19242,plain,(
    g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = sK45(sK35) ),
    inference(subsumption_resolution,[],[f19218,f18780])).

fof(f18780,plain,(
    ~ v1_tex_2(sK45(sK35),sK35) ),
    inference(subsumption_resolution,[],[f18779,f4556])).

fof(f18779,plain,
    ( ~ v1_tex_2(sK45(sK35),sK35)
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f18778,f4557])).

fof(f18778,plain,
    ( ~ v1_tex_2(sK45(sK35),sK35)
    | ~ v7_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f18777,f6534])).

fof(f18777,plain,
    ( ~ v1_tex_2(sK45(sK35),sK35)
    | ~ l1_pre_topc(sK35)
    | ~ v7_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f18603,f7015])).

fof(f7015,plain,(
    ~ v2_struct_0(sK45(sK35)) ),
    inference(subsumption_resolution,[],[f6822,f4556])).

fof(f6822,plain,
    ( ~ v2_struct_0(sK45(sK35))
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6534,f4656])).

fof(f4656,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK45(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4226])).

fof(f4226,plain,(
    ! [X0] :
      ( ( v1_pre_topc(sK45(X0))
        & v7_struct_0(sK45(X0))
        & ~ v2_struct_0(sK45(X0))
        & m1_pre_topc(sK45(X0),X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK45])],[f3711,f4225])).

fof(f4225,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
     => ( v1_pre_topc(sK45(X0))
        & v7_struct_0(sK45(X0))
        & ~ v2_struct_0(sK45(X0))
        & m1_pre_topc(sK45(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3711,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3710])).

fof(f3710,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3606])).

fof(f3606,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc8_tex_2)).

fof(f18603,plain,
    ( ~ v1_tex_2(sK45(sK35),sK35)
    | v2_struct_0(sK45(sK35))
    | ~ l1_pre_topc(sK35)
    | ~ v7_struct_0(sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f7014,f4706])).

fof(f4706,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3745])).

fof(f3745,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3744])).

fof(f3744,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3540])).

fof(f3540,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f7014,plain,(
    m1_pre_topc(sK45(sK35),sK35) ),
    inference(subsumption_resolution,[],[f6821,f4556])).

fof(f6821,plain,
    ( m1_pre_topc(sK45(sK35),sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6534,f4655])).

fof(f4655,plain,(
    ! [X0] :
      ( m1_pre_topc(sK45(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4226])).

fof(f19218,plain,
    ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = sK45(sK35)
    | v1_tex_2(sK45(sK35),sK35) ),
    inference(backward_demodulation,[],[f18776,f19204])).

fof(f19204,plain,(
    sK45(sK35) = g1_pre_topc(u1_struct_0(sK45(sK35)),u1_pre_topc(sK45(sK35))) ),
    inference(subsumption_resolution,[],[f18995,f7017])).

fof(f7017,plain,(
    v1_pre_topc(sK45(sK35)) ),
    inference(subsumption_resolution,[],[f6824,f4556])).

fof(f6824,plain,
    ( v1_pre_topc(sK45(sK35))
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f6534,f4658])).

fof(f4658,plain,(
    ! [X0] :
      ( v1_pre_topc(sK45(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4226])).

fof(f18995,plain,
    ( sK45(sK35) = g1_pre_topc(u1_struct_0(sK45(sK35)),u1_pre_topc(sK45(sK35)))
    | ~ v1_pre_topc(sK45(sK35)) ),
    inference(resolution,[],[f18728,f4609])).

fof(f4609,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3685])).

fof(f3685,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3684])).

fof(f3684,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f18728,plain,(
    l1_pre_topc(sK45(sK35)) ),
    inference(subsumption_resolution,[],[f18585,f6534])).

fof(f18585,plain,
    ( l1_pre_topc(sK45(sK35))
    | ~ l1_pre_topc(sK35) ),
    inference(resolution,[],[f7014,f4629])).

fof(f18776,plain,
    ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = g1_pre_topc(u1_struct_0(sK45(sK35)),u1_pre_topc(sK45(sK35)))
    | v1_tex_2(sK45(sK35),sK35) ),
    inference(subsumption_resolution,[],[f18775,f4556])).

fof(f18775,plain,
    ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = g1_pre_topc(u1_struct_0(sK45(sK35)),u1_pre_topc(sK45(sK35)))
    | v1_tex_2(sK45(sK35),sK35)
    | v2_struct_0(sK35) ),
    inference(subsumption_resolution,[],[f18601,f6534])).

fof(f18601,plain,
    ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = g1_pre_topc(u1_struct_0(sK45(sK35)),u1_pre_topc(sK45(sK35)))
    | v1_tex_2(sK45(sK35),sK35)
    | ~ l1_pre_topc(sK35)
    | v2_struct_0(sK35) ),
    inference(resolution,[],[f7014,f4702])).

fof(f4702,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3741])).

fof(f3741,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3740])).

fof(f3740,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3614])).

fof(f3614,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tex_2)).

fof(f4559,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK34))
      | g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X2)),u1_pre_topc(k1_tex_2(sK34,X2))) != g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) ) ),
    inference(cnf_transformation,[],[f4192])).

fof(f40499,plain,(
    ! [X22] :
      ( u1_struct_0(sK35) != u1_struct_0(k1_tex_2(sK34,X22))
      | sK45(sK35) = g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X22)),u1_pre_topc(k1_tex_2(sK34,X22)))
      | ~ m1_subset_1(X22,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f40498,f4554])).

fof(f40498,plain,(
    ! [X22] :
      ( u1_struct_0(sK35) != u1_struct_0(k1_tex_2(sK34,X22))
      | sK45(sK35) = g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X22)),u1_pre_topc(k1_tex_2(sK34,X22)))
      | ~ m1_subset_1(X22,u1_struct_0(sK34))
      | v2_struct_0(sK34) ) ),
    inference(subsumption_resolution,[],[f40457,f4555])).

fof(f40457,plain,(
    ! [X22] :
      ( u1_struct_0(sK35) != u1_struct_0(k1_tex_2(sK34,X22))
      | sK45(sK35) = g1_pre_topc(u1_struct_0(k1_tex_2(sK34,X22)),u1_pre_topc(k1_tex_2(sK34,X22)))
      | ~ m1_subset_1(X22,u1_struct_0(sK34))
      | ~ l1_pre_topc(sK34)
      | v2_struct_0(sK34) ) ),
    inference(resolution,[],[f19253,f4562])).

fof(f19253,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK34)
      | u1_struct_0(sK35) != u1_struct_0(X6)
      | sK45(sK35) = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) ) ),
    inference(backward_demodulation,[],[f6502,f19242])).

fof(f6502,plain,(
    ! [X6] :
      ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | u1_struct_0(sK35) != u1_struct_0(X6)
      | ~ m1_pre_topc(X6,sK34) ) ),
    inference(subsumption_resolution,[],[f6366,f4555])).

fof(f6366,plain,(
    ! [X6] :
      ( g1_pre_topc(u1_struct_0(sK35),u1_pre_topc(sK35)) = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))
      | u1_struct_0(sK35) != u1_struct_0(X6)
      | ~ m1_pre_topc(X6,sK34)
      | ~ l1_pre_topc(sK34) ) ),
    inference(resolution,[],[f4558,f4601])).

fof(f4601,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3675])).

fof(f3675,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3674])).

fof(f3674,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3492])).

fof(f3492,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).
%------------------------------------------------------------------------------
