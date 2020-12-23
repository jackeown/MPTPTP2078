%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:47 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 196 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  233 ( 444 expanded)
%              Number of equality atoms :   40 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f134,f183])).

fof(f183,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f181,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f181,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f177,f161])).

fof(f161,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f45,f158])).

fof(f158,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f115,f157])).

fof(f157,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f154,f127])).

fof(f127,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f102,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f90,f99])).

fof(f99,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f91,plain,(
    ! [X2] : r1_tarski(k1_struct_0(sK0),X2) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f72])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f83,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_struct_0(X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_struct_0(X1))) ) ),
    inference(resolution,[],[f69,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f90,plain,(
    ! [X1] : r1_xboole_0(X1,k1_struct_0(sK0)) ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

% (13929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f154,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f115,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f177,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f176,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_pre_topc(sK0,X0),X0)
      | k2_pre_topc(sK0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f152,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f152,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f176,plain,(
    r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f171,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f171,plain,(
    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f170,f72])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f134,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f111,f51])).

fof(f111,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f106,f113,f109])).

fof(f106,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f50,f99])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (823001089)
% 0.21/0.37  ipcrm: permission denied for id (819265538)
% 0.21/0.37  ipcrm: permission denied for id (818216963)
% 0.21/0.37  ipcrm: permission denied for id (819298308)
% 0.21/0.37  ipcrm: permission denied for id (819331077)
% 0.21/0.37  ipcrm: permission denied for id (819363846)
% 0.21/0.37  ipcrm: permission denied for id (819396615)
% 0.21/0.38  ipcrm: permission denied for id (818282505)
% 0.21/0.38  ipcrm: permission denied for id (823066634)
% 0.21/0.38  ipcrm: permission denied for id (823099403)
% 0.21/0.38  ipcrm: permission denied for id (823132172)
% 0.21/0.38  ipcrm: permission denied for id (823164941)
% 0.21/0.38  ipcrm: permission denied for id (819593230)
% 0.21/0.38  ipcrm: permission denied for id (819625999)
% 0.21/0.38  ipcrm: permission denied for id (819658768)
% 0.21/0.39  ipcrm: permission denied for id (819691537)
% 0.21/0.39  ipcrm: permission denied for id (823230483)
% 0.21/0.39  ipcrm: permission denied for id (819822613)
% 0.21/0.39  ipcrm: permission denied for id (819888151)
% 0.21/0.39  ipcrm: permission denied for id (823328792)
% 0.21/0.40  ipcrm: permission denied for id (823361561)
% 0.21/0.40  ipcrm: permission denied for id (819986458)
% 0.21/0.40  ipcrm: permission denied for id (820019227)
% 0.21/0.40  ipcrm: permission denied for id (820051996)
% 0.21/0.40  ipcrm: permission denied for id (820084765)
% 0.21/0.40  ipcrm: permission denied for id (818380830)
% 0.21/0.40  ipcrm: permission denied for id (820117535)
% 0.21/0.40  ipcrm: permission denied for id (818413600)
% 0.21/0.41  ipcrm: permission denied for id (823394337)
% 0.21/0.41  ipcrm: permission denied for id (818446373)
% 0.21/0.41  ipcrm: permission denied for id (820314151)
% 0.21/0.41  ipcrm: permission denied for id (820346920)
% 0.21/0.42  ipcrm: permission denied for id (823558185)
% 0.21/0.42  ipcrm: permission denied for id (820412458)
% 0.21/0.42  ipcrm: permission denied for id (820445227)
% 0.21/0.42  ipcrm: permission denied for id (820477996)
% 0.21/0.42  ipcrm: permission denied for id (820510765)
% 0.21/0.42  ipcrm: permission denied for id (820543534)
% 0.21/0.42  ipcrm: permission denied for id (820576303)
% 0.21/0.43  ipcrm: permission denied for id (820609072)
% 0.21/0.43  ipcrm: permission denied for id (820641841)
% 0.21/0.43  ipcrm: permission denied for id (820674610)
% 0.21/0.43  ipcrm: permission denied for id (820707379)
% 0.21/0.43  ipcrm: permission denied for id (823590964)
% 0.21/0.43  ipcrm: permission denied for id (820772917)
% 0.21/0.43  ipcrm: permission denied for id (820805686)
% 0.21/0.43  ipcrm: permission denied for id (818577463)
% 0.21/0.44  ipcrm: permission denied for id (818610232)
% 0.21/0.44  ipcrm: permission denied for id (820871226)
% 0.21/0.44  ipcrm: permission denied for id (820936763)
% 0.21/0.44  ipcrm: permission denied for id (820969532)
% 0.21/0.44  ipcrm: permission denied for id (821035070)
% 0.21/0.45  ipcrm: permission denied for id (823722048)
% 0.21/0.45  ipcrm: permission denied for id (823754817)
% 0.21/0.45  ipcrm: permission denied for id (821166146)
% 0.21/0.45  ipcrm: permission denied for id (823853125)
% 0.21/0.46  ipcrm: permission denied for id (823918663)
% 0.21/0.46  ipcrm: permission denied for id (821362760)
% 0.21/0.46  ipcrm: permission denied for id (823951433)
% 0.21/0.46  ipcrm: permission denied for id (821428298)
% 0.21/0.46  ipcrm: permission denied for id (821493836)
% 0.21/0.46  ipcrm: permission denied for id (821559374)
% 0.21/0.47  ipcrm: permission denied for id (824049743)
% 0.21/0.47  ipcrm: permission denied for id (821624912)
% 0.21/0.47  ipcrm: permission denied for id (818708561)
% 0.21/0.47  ipcrm: permission denied for id (818741330)
% 0.21/0.47  ipcrm: permission denied for id (821657683)
% 0.21/0.47  ipcrm: permission denied for id (824082516)
% 0.21/0.47  ipcrm: permission denied for id (821723221)
% 0.21/0.48  ipcrm: permission denied for id (821854297)
% 0.21/0.48  ipcrm: permission denied for id (821887066)
% 0.21/0.48  ipcrm: permission denied for id (821919835)
% 0.21/0.48  ipcrm: permission denied for id (821952604)
% 0.21/0.48  ipcrm: permission denied for id (821985373)
% 0.21/0.48  ipcrm: permission denied for id (824213598)
% 0.21/0.49  ipcrm: permission denied for id (822050911)
% 0.21/0.49  ipcrm: permission denied for id (822083680)
% 0.21/0.49  ipcrm: permission denied for id (824246369)
% 0.21/0.49  ipcrm: permission denied for id (818905186)
% 0.21/0.49  ipcrm: permission denied for id (824279139)
% 0.21/0.49  ipcrm: permission denied for id (822181988)
% 0.21/0.49  ipcrm: permission denied for id (822214757)
% 0.21/0.49  ipcrm: permission denied for id (818937958)
% 0.21/0.50  ipcrm: permission denied for id (824311911)
% 0.21/0.50  ipcrm: permission denied for id (822280296)
% 0.21/0.50  ipcrm: permission denied for id (822313065)
% 0.21/0.50  ipcrm: permission denied for id (822378603)
% 0.21/0.50  ipcrm: permission denied for id (822411372)
% 0.21/0.50  ipcrm: permission denied for id (824377453)
% 0.21/0.51  ipcrm: permission denied for id (824442991)
% 0.21/0.51  ipcrm: permission denied for id (822542448)
% 0.21/0.51  ipcrm: permission denied for id (822607986)
% 0.21/0.51  ipcrm: permission denied for id (822640755)
% 0.21/0.51  ipcrm: permission denied for id (822706293)
% 0.21/0.52  ipcrm: permission denied for id (824541302)
% 0.21/0.52  ipcrm: permission denied for id (819101815)
% 0.21/0.52  ipcrm: permission denied for id (824574072)
% 0.21/0.52  ipcrm: permission denied for id (819134585)
% 0.21/0.52  ipcrm: permission denied for id (824606842)
% 0.21/0.52  ipcrm: permission denied for id (819167356)
% 0.21/0.53  ipcrm: permission denied for id (824705150)
% 0.21/0.53  ipcrm: permission denied for id (824737919)
% 0.85/0.68  % (13927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.85/0.68  % (13938)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.85/0.68  % (13927)Refutation found. Thanks to Tanya!
% 0.85/0.68  % SZS status Theorem for theBenchmark
% 0.85/0.68  % SZS output start Proof for theBenchmark
% 0.85/0.68  fof(f185,plain,(
% 0.85/0.68    $false),
% 0.85/0.68    inference(avatar_sat_refutation,[],[f116,f134,f183])).
% 0.85/0.68  fof(f183,plain,(
% 0.85/0.68    ~spl3_2),
% 0.85/0.68    inference(avatar_contradiction_clause,[],[f182])).
% 0.85/0.68  fof(f182,plain,(
% 0.85/0.68    $false | ~spl3_2),
% 0.85/0.68    inference(subsumption_resolution,[],[f181,f72])).
% 0.85/0.68  fof(f72,plain,(
% 0.85/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.85/0.68    inference(forward_demodulation,[],[f48,f47])).
% 0.85/0.68  fof(f47,plain,(
% 0.85/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.85/0.68    inference(cnf_transformation,[],[f7])).
% 0.85/0.68  fof(f7,axiom,(
% 0.85/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.85/0.68  fof(f48,plain,(
% 0.85/0.68    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.85/0.68    inference(cnf_transformation,[],[f9])).
% 0.85/0.68  fof(f9,axiom,(
% 0.85/0.68    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.85/0.68  fof(f181,plain,(
% 0.85/0.68    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.85/0.68    inference(subsumption_resolution,[],[f177,f161])).
% 0.85/0.68  fof(f161,plain,(
% 0.85/0.68    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) | ~spl3_2),
% 0.85/0.68    inference(backward_demodulation,[],[f45,f158])).
% 0.85/0.68  fof(f158,plain,(
% 0.85/0.68    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_2),
% 0.85/0.68    inference(backward_demodulation,[],[f115,f157])).
% 0.85/0.68  fof(f157,plain,(
% 0.85/0.68    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.85/0.68    inference(forward_demodulation,[],[f154,f127])).
% 0.85/0.68  fof(f127,plain,(
% 0.85/0.68    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.85/0.68    inference(resolution,[],[f102,f62])).
% 0.85/0.68  fof(f62,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.85/0.68    inference(cnf_transformation,[],[f38])).
% 0.85/0.68  fof(f38,plain,(
% 0.85/0.68    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.85/0.68    inference(nnf_transformation,[],[f6])).
% 0.85/0.68  fof(f6,axiom,(
% 0.85/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.85/0.68  fof(f102,plain,(
% 0.85/0.68    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.85/0.68    inference(backward_demodulation,[],[f90,f99])).
% 0.85/0.68  fof(f99,plain,(
% 0.85/0.68    k1_xboole_0 = k1_struct_0(sK0)),
% 0.85/0.68    inference(resolution,[],[f91,f53])).
% 0.85/0.68  fof(f53,plain,(
% 0.85/0.68    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.85/0.68    inference(cnf_transformation,[],[f25])).
% 0.85/0.68  fof(f25,plain,(
% 0.85/0.68    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.85/0.68    inference(ennf_transformation,[],[f5])).
% 0.85/0.68  fof(f5,axiom,(
% 0.85/0.68    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.85/0.68  fof(f91,plain,(
% 0.85/0.68    ( ! [X2] : (r1_tarski(k1_struct_0(sK0),X2)) )),
% 0.85/0.68    inference(resolution,[],[f87,f65])).
% 0.85/0.68  fof(f65,plain,(
% 0.85/0.68    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f42])).
% 0.85/0.68  fof(f42,plain,(
% 0.85/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.85/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 0.85/0.68  fof(f41,plain,(
% 0.85/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.85/0.68    introduced(choice_axiom,[])).
% 0.85/0.68  fof(f40,plain,(
% 0.85/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.85/0.68    inference(rectify,[],[f39])).
% 0.85/0.68  fof(f39,plain,(
% 0.85/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.85/0.68    inference(nnf_transformation,[],[f30])).
% 0.85/0.68  fof(f30,plain,(
% 0.85/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.85/0.68    inference(ennf_transformation,[],[f1])).
% 0.85/0.68  fof(f1,axiom,(
% 0.85/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.85/0.68  fof(f87,plain,(
% 0.85/0.68    ( ! [X0] : (~r2_hidden(X0,k1_struct_0(sK0))) )),
% 0.85/0.68    inference(resolution,[],[f84,f72])).
% 0.85/0.68  fof(f84,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.85/0.68    inference(resolution,[],[f83,f44])).
% 0.85/0.68  fof(f44,plain,(
% 0.85/0.68    l1_pre_topc(sK0)),
% 0.85/0.68    inference(cnf_transformation,[],[f33])).
% 0.85/0.68  fof(f33,plain,(
% 0.85/0.68    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.85/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).
% 0.85/0.68  fof(f32,plain,(
% 0.85/0.68    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0)) => (k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.85/0.68    introduced(choice_axiom,[])).
% 0.85/0.68  fof(f20,plain,(
% 0.85/0.68    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.85/0.68    inference(ennf_transformation,[],[f18])).
% 0.85/0.68  fof(f18,negated_conjecture,(
% 0.85/0.68    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.85/0.68    inference(negated_conjecture,[],[f17])).
% 0.85/0.68  fof(f17,conjecture,(
% 0.85/0.68    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 0.85/0.68  fof(f83,plain,(
% 0.85/0.68    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_struct_0(X2))) | ~r2_hidden(X0,X1)) )),
% 0.85/0.68    inference(resolution,[],[f82,f51])).
% 0.85/0.68  fof(f51,plain,(
% 0.85/0.68    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f23])).
% 0.85/0.68  fof(f23,plain,(
% 0.85/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.85/0.68    inference(ennf_transformation,[],[f13])).
% 0.85/0.68  fof(f13,axiom,(
% 0.85/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.85/0.68  fof(f82,plain,(
% 0.85/0.68    ( ! [X2,X0,X1] : (~l1_struct_0(X1) | ~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_struct_0(X1)))) )),
% 0.85/0.68    inference(resolution,[],[f69,f49])).
% 0.85/0.68  fof(f49,plain,(
% 0.85/0.68    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f21])).
% 0.85/0.68  fof(f21,plain,(
% 0.85/0.68    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.85/0.68    inference(ennf_transformation,[],[f14])).
% 0.85/0.68  fof(f14,axiom,(
% 0.85/0.68    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).
% 0.85/0.68  fof(f69,plain,(
% 0.85/0.68    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f31])).
% 0.85/0.68  fof(f31,plain,(
% 0.85/0.68    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.85/0.68    inference(ennf_transformation,[],[f11])).
% 0.85/0.68  fof(f11,axiom,(
% 0.85/0.68    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.85/0.68  fof(f90,plain,(
% 0.85/0.68    ( ! [X1] : (r1_xboole_0(X1,k1_struct_0(sK0))) )),
% 0.85/0.68    inference(resolution,[],[f87,f55])).
% 0.85/0.68  fof(f55,plain,(
% 0.85/0.68    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f35])).
% 0.85/0.68  fof(f35,plain,(
% 0.85/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.85/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).
% 0.85/0.68  fof(f34,plain,(
% 0.85/0.68    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.85/0.68    introduced(choice_axiom,[])).
% 0.85/0.68  fof(f26,plain,(
% 0.85/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.85/0.68    inference(ennf_transformation,[],[f19])).
% 0.85/0.68  fof(f19,plain,(
% 0.85/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.85/0.68    inference(rectify,[],[f2])).
% 0.85/0.68  % (13929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.85/0.68  fof(f2,axiom,(
% 0.85/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.85/0.68  fof(f154,plain,(
% 0.85/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.85/0.68    inference(resolution,[],[f86,f46])).
% 0.85/0.68  fof(f46,plain,(
% 0.85/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f4])).
% 0.85/0.68  fof(f4,axiom,(
% 0.85/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.85/0.68  fof(f86,plain,(
% 0.85/0.68    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 0.85/0.68    inference(resolution,[],[f57,f68])).
% 0.85/0.68  fof(f68,plain,(
% 0.85/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f43])).
% 0.85/0.68  fof(f43,plain,(
% 0.85/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.85/0.68    inference(nnf_transformation,[],[f10])).
% 0.85/0.68  fof(f10,axiom,(
% 0.85/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.85/0.68  fof(f57,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f27])).
% 0.85/0.68  fof(f27,plain,(
% 0.85/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.85/0.68    inference(ennf_transformation,[],[f8])).
% 0.85/0.68  fof(f8,axiom,(
% 0.85/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.85/0.68  fof(f115,plain,(
% 0.85/0.68    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl3_2),
% 0.85/0.68    inference(avatar_component_clause,[],[f113])).
% 0.85/0.68  fof(f113,plain,(
% 0.85/0.68    spl3_2 <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.85/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.85/0.68  fof(f45,plain,(
% 0.85/0.68    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.85/0.68    inference(cnf_transformation,[],[f33])).
% 0.85/0.68  fof(f177,plain,(
% 0.85/0.68    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.85/0.68    inference(resolution,[],[f176,f153])).
% 0.85/0.68  fof(f153,plain,(
% 0.85/0.68    ( ! [X0] : (~r1_tarski(k2_pre_topc(sK0,X0),X0) | k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.85/0.68    inference(resolution,[],[f152,f61])).
% 0.85/0.68  fof(f61,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f37])).
% 0.85/0.68  fof(f37,plain,(
% 0.85/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.85/0.68    inference(flattening,[],[f36])).
% 0.85/0.68  fof(f36,plain,(
% 0.85/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.85/0.68    inference(nnf_transformation,[],[f3])).
% 0.85/0.68  fof(f3,axiom,(
% 0.85/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.85/0.68  fof(f152,plain,(
% 0.85/0.68    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.85/0.68    inference(resolution,[],[f52,f44])).
% 0.85/0.68  fof(f52,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.85/0.68    inference(cnf_transformation,[],[f24])).
% 0.85/0.68  fof(f24,plain,(
% 0.85/0.68    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/0.68    inference(ennf_transformation,[],[f16])).
% 0.85/0.68  fof(f16,axiom,(
% 0.85/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.85/0.68  fof(f176,plain,(
% 0.85/0.68    r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.85/0.68    inference(resolution,[],[f171,f67])).
% 0.85/0.68  fof(f67,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f43])).
% 0.85/0.68  fof(f171,plain,(
% 0.85/0.68    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.85/0.68    inference(resolution,[],[f170,f72])).
% 0.85/0.68  fof(f170,plain,(
% 0.85/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.85/0.68    inference(resolution,[],[f58,f44])).
% 0.85/0.68  fof(f58,plain,(
% 0.85/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.85/0.68    inference(cnf_transformation,[],[f29])).
% 0.85/0.68  fof(f29,plain,(
% 0.85/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.85/0.68    inference(flattening,[],[f28])).
% 0.85/0.68  fof(f28,plain,(
% 0.85/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.85/0.68    inference(ennf_transformation,[],[f12])).
% 0.85/0.68  fof(f12,axiom,(
% 0.85/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.85/0.68  fof(f134,plain,(
% 0.85/0.68    spl3_1),
% 0.85/0.68    inference(avatar_contradiction_clause,[],[f133])).
% 0.85/0.68  fof(f133,plain,(
% 0.85/0.68    $false | spl3_1),
% 0.85/0.68    inference(subsumption_resolution,[],[f132,f44])).
% 0.85/0.68  fof(f132,plain,(
% 0.85/0.68    ~l1_pre_topc(sK0) | spl3_1),
% 0.85/0.68    inference(resolution,[],[f111,f51])).
% 0.85/0.68  fof(f111,plain,(
% 0.85/0.68    ~l1_struct_0(sK0) | spl3_1),
% 0.85/0.68    inference(avatar_component_clause,[],[f109])).
% 0.85/0.68  fof(f109,plain,(
% 0.85/0.68    spl3_1 <=> l1_struct_0(sK0)),
% 0.85/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.85/0.68  fof(f116,plain,(
% 0.85/0.68    ~spl3_1 | spl3_2),
% 0.85/0.68    inference(avatar_split_clause,[],[f106,f113,f109])).
% 0.85/0.68  fof(f106,plain,(
% 0.85/0.68    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~l1_struct_0(sK0)),
% 0.85/0.68    inference(superposition,[],[f50,f99])).
% 0.85/0.68  fof(f50,plain,(
% 0.85/0.68    ( ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.85/0.68    inference(cnf_transformation,[],[f22])).
% 0.85/0.68  fof(f22,plain,(
% 0.85/0.68    ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.85/0.68    inference(ennf_transformation,[],[f15])).
% 0.85/0.68  fof(f15,axiom,(
% 0.85/0.68    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)))),
% 0.85/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).
% 0.85/0.68  % SZS output end Proof for theBenchmark
% 0.85/0.68  % (13927)------------------------------
% 0.85/0.68  % (13927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.68  % (13927)Termination reason: Refutation
% 0.85/0.68  
% 0.85/0.68  % (13927)Memory used [KB]: 10746
% 0.85/0.68  % (13927)Time elapsed: 0.111 s
% 0.85/0.68  % (13927)------------------------------
% 0.85/0.68  % (13927)------------------------------
% 0.85/0.69  % (13941)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.85/0.69  % (13943)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.85/0.69  % (13953)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.85/0.69  % (13928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.85/0.69  % (13924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.85/0.69  % (13931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.85/0.69  % (13945)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.85/0.69  % (13939)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.85/0.69  % (13947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.85/0.69  % (13947)Refutation not found, incomplete strategy% (13947)------------------------------
% 0.85/0.69  % (13947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.69  % (13947)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.69  
% 0.85/0.69  % (13945)Refutation not found, incomplete strategy% (13945)------------------------------
% 0.85/0.69  % (13945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.69  % (13947)Memory used [KB]: 10618
% 0.85/0.69  % (13947)Time elapsed: 0.084 s
% 0.85/0.69  % (13945)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.69  
% 0.85/0.69  % (13947)------------------------------
% 0.85/0.69  % (13947)------------------------------
% 0.85/0.69  % (13945)Memory used [KB]: 10746
% 0.85/0.69  % (13945)Time elapsed: 0.126 s
% 0.85/0.69  % (13945)------------------------------
% 0.85/0.69  % (13945)------------------------------
% 0.85/0.69  % (13925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.85/0.69  % (13944)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.85/0.69  % (13926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.85/0.70  % (13948)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.85/0.70  % (13926)Refutation not found, incomplete strategy% (13926)------------------------------
% 0.85/0.70  % (13926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.70  % (13926)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.70  
% 0.85/0.70  % (13926)Memory used [KB]: 10618
% 0.85/0.70  % (13926)Time elapsed: 0.106 s
% 0.85/0.70  % (13926)------------------------------
% 0.85/0.70  % (13926)------------------------------
% 0.85/0.70  % (13952)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.85/0.70  % (13940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.85/0.70  % (13946)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.85/0.70  % (13949)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.85/0.70  % (13946)Refutation not found, incomplete strategy% (13946)------------------------------
% 0.85/0.70  % (13946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.70  % (13946)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.70  
% 0.85/0.70  % (13946)Memory used [KB]: 1663
% 0.85/0.70  % (13946)Time elapsed: 0.119 s
% 0.85/0.70  % (13946)------------------------------
% 0.85/0.70  % (13946)------------------------------
% 0.85/0.70  % (13934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.85/0.70  % (13934)Refutation not found, incomplete strategy% (13934)------------------------------
% 0.85/0.70  % (13934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.70  % (13934)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.70  
% 0.85/0.70  % (13934)Memory used [KB]: 10618
% 0.85/0.70  % (13934)Time elapsed: 0.132 s
% 0.85/0.70  % (13934)------------------------------
% 0.85/0.70  % (13934)------------------------------
% 0.85/0.70  % (13734)Success in time 0.34 s
%------------------------------------------------------------------------------
