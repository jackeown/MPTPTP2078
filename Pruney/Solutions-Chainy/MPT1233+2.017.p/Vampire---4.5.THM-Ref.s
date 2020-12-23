%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:58 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 124 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 ( 279 expanded)
%              Number of equality atoms :   64 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f304,f80])).

fof(f80,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f35,f79])).

fof(f79,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f76,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f35,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f304,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f303,f64])).

fof(f64,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f303,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f302,f108])).

fof(f108,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f107,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f106,f105])).

fof(f105,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(resolution,[],[f103,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f102,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f106,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f302,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f296,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f90,f64])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f296,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f290,f125])).

fof(f125,plain,(
    ! [X6] : r1_tarski(X6,X6) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X6,X6) ) ),
    inference(superposition,[],[f65,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f290,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f269,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f269,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (12257)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (12265)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (12273)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (12273)Refutation not found, incomplete strategy% (12273)------------------------------
% 0.22/0.56  % (12273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12259)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (12259)Refutation not found, incomplete strategy% (12259)------------------------------
% 0.22/0.56  % (12259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12259)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12259)Memory used [KB]: 10618
% 0.22/0.56  % (12259)Time elapsed: 0.131 s
% 0.22/0.56  % (12259)------------------------------
% 0.22/0.56  % (12259)------------------------------
% 0.22/0.56  % (12273)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  % (12275)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.57  % (12267)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.57  
% 1.41/0.57  % (12273)Memory used [KB]: 10746
% 1.41/0.57  % (12273)Time elapsed: 0.122 s
% 1.41/0.57  % (12273)------------------------------
% 1.41/0.57  % (12273)------------------------------
% 1.41/0.57  % (12257)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f305,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(subsumption_resolution,[],[f304,f80])).
% 1.41/0.57  fof(f80,plain,(
% 1.41/0.57    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.41/0.57    inference(backward_demodulation,[],[f35,f79])).
% 1.41/0.57  fof(f79,plain,(
% 1.41/0.57    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.41/0.57    inference(resolution,[],[f76,f34])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    l1_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f21])).
% 1.41/0.57  fof(f21,plain,(
% 1.41/0.57    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f20])).
% 1.41/0.57  fof(f20,plain,(
% 1.41/0.57    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f19])).
% 1.41/0.57  fof(f19,negated_conjecture,(
% 1.41/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.41/0.57    inference(negated_conjecture,[],[f18])).
% 1.41/0.57  fof(f18,conjecture,(
% 1.41/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.41/0.57  fof(f76,plain,(
% 1.41/0.57    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.41/0.57    inference(resolution,[],[f41,f42])).
% 1.41/0.57  fof(f42,plain,(
% 1.41/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f23])).
% 1.41/0.57  fof(f23,plain,(
% 1.41/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f15])).
% 1.41/0.57  fof(f15,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.41/0.57  fof(f41,plain,(
% 1.41/0.57    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f22,plain,(
% 1.41/0.57    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f14])).
% 1.41/0.57  fof(f14,axiom,(
% 1.41/0.57    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.41/0.57    inference(cnf_transformation,[],[f21])).
% 1.41/0.57  fof(f304,plain,(
% 1.41/0.57    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.41/0.57    inference(forward_demodulation,[],[f303,f64])).
% 1.41/0.57  fof(f64,plain,(
% 1.41/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.41/0.57    inference(definition_unfolding,[],[f38,f63])).
% 1.41/0.57  fof(f63,plain,(
% 1.41/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f40,f37])).
% 1.41/0.57  fof(f37,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f5])).
% 1.41/0.57  fof(f5,axiom,(
% 1.41/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.41/0.57  fof(f40,plain,(
% 1.41/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f8])).
% 1.41/0.57  fof(f8,axiom,(
% 1.41/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.41/0.57  fof(f38,plain,(
% 1.41/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f6])).
% 1.41/0.57  fof(f6,axiom,(
% 1.41/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.41/0.57  fof(f303,plain,(
% 1.41/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 1.41/0.57    inference(forward_demodulation,[],[f302,f108])).
% 1.41/0.57  fof(f108,plain,(
% 1.41/0.57    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.41/0.57    inference(subsumption_resolution,[],[f107,f39])).
% 1.41/0.57  fof(f39,plain,(
% 1.41/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f9])).
% 1.41/0.57  fof(f9,axiom,(
% 1.41/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.41/0.57  fof(f107,plain,(
% 1.41/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.41/0.57    inference(resolution,[],[f106,f105])).
% 1.41/0.57  fof(f105,plain,(
% 1.41/0.57    v4_pre_topc(k1_xboole_0,sK0)),
% 1.41/0.57    inference(subsumption_resolution,[],[f104,f39])).
% 1.41/0.57  fof(f104,plain,(
% 1.41/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 1.41/0.57    inference(resolution,[],[f103,f36])).
% 1.41/0.57  fof(f36,plain,(
% 1.41/0.57    v1_xboole_0(k1_xboole_0)),
% 1.41/0.57    inference(cnf_transformation,[],[f2])).
% 1.41/0.57  fof(f2,axiom,(
% 1.41/0.57    v1_xboole_0(k1_xboole_0)),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.57  fof(f103,plain,(
% 1.41/0.57    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.41/0.57    inference(subsumption_resolution,[],[f102,f33])).
% 1.41/0.57  fof(f33,plain,(
% 1.41/0.57    v2_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f21])).
% 1.41/0.57  fof(f102,plain,(
% 1.41/0.57    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v4_pre_topc(X0,sK0)) )),
% 1.41/0.57    inference(resolution,[],[f46,f34])).
% 1.41/0.57  fof(f46,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f28])).
% 1.41/0.57  fof(f28,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f27])).
% 1.41/0.57  fof(f27,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f13])).
% 1.41/0.57  fof(f13,axiom,(
% 1.41/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.41/0.57  fof(f106,plain,(
% 1.41/0.57    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 1.41/0.57    inference(resolution,[],[f45,f34])).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f26])).
% 1.41/0.57  fof(f26,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(flattening,[],[f25])).
% 1.41/0.57  fof(f25,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f16])).
% 1.41/0.57  fof(f16,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.41/0.57  fof(f302,plain,(
% 1.41/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 1.41/0.57    inference(forward_demodulation,[],[f296,f92])).
% 1.41/0.57  fof(f92,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.41/0.57    inference(forward_demodulation,[],[f90,f64])).
% 1.41/0.57  fof(f90,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.41/0.57    inference(resolution,[],[f51,f39])).
% 1.41/0.57  fof(f51,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f30])).
% 1.41/0.57  fof(f30,plain,(
% 1.41/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f7])).
% 1.41/0.57  fof(f7,axiom,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.41/0.57  fof(f296,plain,(
% 1.41/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.41/0.57    inference(resolution,[],[f290,f125])).
% 1.41/0.57  fof(f125,plain,(
% 1.41/0.57    ( ! [X6] : (r1_tarski(X6,X6)) )),
% 1.41/0.57    inference(trivial_inequality_removal,[],[f124])).
% 1.41/0.57  fof(f124,plain,(
% 1.41/0.57    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X6,X6)) )),
% 1.41/0.57    inference(superposition,[],[f65,f119])).
% 1.41/0.57  fof(f119,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f112])).
% 1.41/0.57  fof(f112,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.41/0.57    inference(resolution,[],[f88,f83])).
% 1.41/0.57  fof(f83,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.57    inference(resolution,[],[f74,f49])).
% 1.41/0.57  fof(f49,plain,(
% 1.41/0.57    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f29])).
% 1.41/0.57  fof(f29,plain,(
% 1.41/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.41/0.57    inference(ennf_transformation,[],[f12])).
% 1.41/0.57  fof(f12,axiom,(
% 1.41/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.41/0.57  fof(f74,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.41/0.57    inference(equality_resolution,[],[f68])).
% 1.41/0.57  fof(f68,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.41/0.57    inference(definition_unfolding,[],[f61,f50])).
% 1.41/0.57  fof(f50,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f4])).
% 1.41/0.57  fof(f4,axiom,(
% 1.41/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.57  fof(f61,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f1])).
% 1.41/0.57  fof(f1,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.57  fof(f88,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.57    inference(resolution,[],[f75,f49])).
% 1.41/0.57  fof(f75,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.41/0.57    inference(equality_resolution,[],[f69])).
% 1.41/0.57  fof(f69,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.41/0.57    inference(definition_unfolding,[],[f60,f50])).
% 1.41/0.57  fof(f60,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f1])).
% 1.41/0.57  fof(f65,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f55,f50])).
% 1.41/0.57  fof(f55,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f3])).
% 1.41/0.57  fof(f3,axiom,(
% 1.41/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.41/0.57  fof(f290,plain,(
% 1.41/0.57    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.41/0.57    inference(resolution,[],[f269,f52])).
% 1.41/0.57  fof(f52,plain,(
% 1.41/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f10])).
% 1.41/0.57  fof(f10,axiom,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.57  fof(f269,plain,(
% 1.41/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.41/0.57    inference(resolution,[],[f43,f34])).
% 1.41/0.57  fof(f43,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f24])).
% 1.41/0.57  fof(f24,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.57    inference(ennf_transformation,[],[f17])).
% 1.41/0.57  fof(f17,axiom,(
% 1.41/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.41/0.57  % SZS output end Proof for theBenchmark
% 1.41/0.57  % (12257)------------------------------
% 1.41/0.57  % (12257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (12257)Termination reason: Refutation
% 1.41/0.57  
% 1.41/0.57  % (12257)Memory used [KB]: 6524
% 1.41/0.57  % (12257)Time elapsed: 0.114 s
% 1.41/0.57  % (12257)------------------------------
% 1.41/0.57  % (12257)------------------------------
% 1.41/0.58  % (12250)Success in time 0.208 s
%------------------------------------------------------------------------------
