%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 192 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  189 ( 719 expanded)
%              Number of equality atoms :   50 ( 153 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(subsumption_resolution,[],[f288,f86])).

fof(f86,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f77,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f51,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f51,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1)
          | k4_tarski(X4,X5) != sK0 )
      & r2_hidden(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f288,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f244,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f244,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f50,f243])).

fof(f243,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f242,f86])).

fof(f242,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f215,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f50,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f204,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f204,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f202,f56])).

fof(f202,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f195,f58])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f193,f56])).

fof(f193,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f191,f113])).

fof(f113,plain,
    ( r2_hidden(sK7(sK1,sK2,sK0),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,(
    m1_subset_1(sK7(sK1,sK2,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f51,f80,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | m1_subset_1(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3
        & m1_subset_1(sK8(X0,X1,X3),X1)
        & m1_subset_1(sK7(X0,X1,X3),X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f32,f48,f47])).

fof(f47,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( k4_tarski(sK7(X0,X1,X3),X5) = X3
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK7(X0,X1,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X1,X0] :
      ( ? [X5] :
          ( k4_tarski(sK7(X0,X1,X3),X5) = X3
          & m1_subset_1(X5,X1) )
     => ( k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3
        & m1_subset_1(sK8(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f80,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f191,plain,
    ( ~ r2_hidden(sK7(sK1,sK2,sK0),sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f158,f117])).

fof(f117,plain,
    ( r2_hidden(sK8(sK1,sK2,sK0),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f96,f61])).

fof(f96,plain,(
    m1_subset_1(sK8(sK1,sK2,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f51,f80,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | m1_subset_1(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f158,plain,
    ( ~ r2_hidden(sK8(sK1,sK2,sK0),sK2)
    | ~ r2_hidden(sK7(sK1,sK2,sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK7(sK1,sK2,sK0),sK1)
    | ~ r2_hidden(sK8(sK1,sK2,sK0),sK2) ),
    inference(superposition,[],[f52,f98])).

fof(f98,plain,(
    sK0 = k4_tarski(sK7(sK1,sK2,sK0),sK8(sK1,sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f80,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f52,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:52:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (21191)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (21179)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (21183)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (21191)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f288,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f77,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    inference(forward_demodulation,[],[f244,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.21/0.49    inference(backward_demodulation,[],[f50,f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f242,f86])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(forward_demodulation,[],[f215,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(superposition,[],[f50,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.49    inference(resolution,[],[f204,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2) )),
% 0.21/0.49    inference(resolution,[],[f202,f56])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 0.21/0.49    inference(resolution,[],[f195,f58])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | v1_xboole_0(sK1)) )),
% 0.21/0.49    inference(resolution,[],[f193,f56])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f191,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r2_hidden(sK7(sK1,sK2,sK0),sK1) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f94,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    m1_subset_1(sK7(sK1,sK2,sK0),sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f80,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | m1_subset_1(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 & m1_subset_1(sK8(X0,X1,X3),X1)) & m1_subset_1(sK7(X0,X1,X3),X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f32,f48,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X3,X1,X0] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (k4_tarski(sK7(X0,X1,X3),X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(sK7(X0,X1,X3),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X3,X1,X0] : (? [X5] : (k4_tarski(sK7(X0,X1,X3),X5) = X3 & m1_subset_1(X5,X1)) => (k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 & m1_subset_1(sK8(X0,X1,X3),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ~r2_hidden(sK7(sK1,sK2,sK0),sK1) | v1_xboole_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f158,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    r2_hidden(sK8(sK1,sK2,sK0),sK2) | v1_xboole_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f96,f61])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    m1_subset_1(sK8(sK1,sK2,sK0),sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f80,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | m1_subset_1(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~r2_hidden(sK8(sK1,sK2,sK0),sK2) | ~r2_hidden(sK7(sK1,sK2,sK0),sK1)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    sK0 != sK0 | ~r2_hidden(sK7(sK1,sK2,sK0),sK1) | ~r2_hidden(sK8(sK1,sK2,sK0),sK2)),
% 0.21/0.49    inference(superposition,[],[f52,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    sK0 = k4_tarski(sK7(sK1,sK2,sK0),sK8(sK1,sK2,sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f51,f80,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21191)------------------------------
% 0.21/0.49  % (21191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21191)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21191)Memory used [KB]: 6268
% 0.21/0.49  % (21191)Time elapsed: 0.021 s
% 0.21/0.49  % (21191)------------------------------
% 0.21/0.49  % (21191)------------------------------
% 0.21/0.50  % (21175)Success in time 0.133 s
%------------------------------------------------------------------------------
