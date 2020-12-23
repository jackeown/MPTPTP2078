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
% DateTime   : Thu Dec  3 12:45:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 ( 443 expanded)
%              Number of equality atoms :   47 (  89 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
          & ~ r2_hidden(X2,sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f162,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f159,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f159,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f37])).

fof(f37,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f158,plain,
    ( r2_hidden(sK2,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f156,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k5_xboole_0(sK0,X0))
      | r2_hidden(sK2,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f59,f63])).

fof(f63,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f156,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f93,f151])).

fof(f151,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f147,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f47,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f69,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f48,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f147,plain,(
    k5_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f49,f146])).

fof(f146,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f145,f43])).

fof(f145,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f48,f144])).

fof(f144,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f143,f54])).

fof(f143,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f139,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | r1_tarski(X4,X3) ) ),
    inference(forward_demodulation,[],[f138,f62])).

fof(f62,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f61,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | r1_tarski(X4,k3_subset_1(X3,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f136,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | r1_tarski(X4,k3_subset_1(X3,k1_xboole_0)) ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f93,plain,(
    ~ r2_hidden(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f38,f91])).

fof(f91,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f38,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (14763)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (14755)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (14747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (14745)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (14749)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (14743)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (14744)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (14759)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (14747)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f162,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f17])).
% 0.20/0.52  fof(f17,conjecture,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f159,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    v1_xboole_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f158,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ~r2_hidden(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    r2_hidden(sK2,sK1) | v1_xboole_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f156,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2,k5_xboole_0(sK0,X0)) | r2_hidden(sK2,X0) | v1_xboole_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f59,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f50,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    m1_subset_1(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.52    inference(nnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ~r2_hidden(sK2,k5_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(backward_demodulation,[],[f93,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(superposition,[],[f147,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(forward_demodulation,[],[f71,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f47,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f69,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(superposition,[],[f48,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f54,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    k5_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.52    inference(superposition,[],[f49,f146])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f145,f43])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 0.20/0.52    inference(superposition,[],[f48,f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f143,f54])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f139,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | r1_tarski(X4,X3)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f138,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(forward_demodulation,[],[f61,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f45,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | r1_tarski(X4,k3_subset_1(X3,k1_xboole_0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f39])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,k3_subset_1(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | r1_tarski(X4,k3_subset_1(X3,k1_xboole_0))) )),
% 0.20/0.52    inference(resolution,[],[f56,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ~r2_hidden(sK2,k4_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(backward_demodulation,[],[f38,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f55,f35])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (14747)------------------------------
% 0.20/0.52  % (14747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14747)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (14747)Memory used [KB]: 6396
% 0.20/0.52  % (14747)Time elapsed: 0.112 s
% 0.20/0.52  % (14747)------------------------------
% 0.20/0.52  % (14747)------------------------------
% 0.20/0.52  % (14740)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (14739)Success in time 0.166 s
%------------------------------------------------------------------------------
