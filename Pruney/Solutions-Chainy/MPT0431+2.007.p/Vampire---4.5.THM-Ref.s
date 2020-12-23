%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:51 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 132 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 576 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f55,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f52,f30])).

fof(f30,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(X1,X0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v3_setfam_1(X2,sK0) )
   => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
           => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f52,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_setfam_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f118,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f117,f54])).

fof(f54,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f28,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,
    ( ~ v3_setfam_1(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f110,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k4_xboole_0(X3,X4))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

% (15900)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X1,X0))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f110,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f106,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f104,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f104,plain,(
    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f103,f31])).

fof(f103,plain,
    ( r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f100,f29])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X6,X4,X5] :
      ( v3_setfam_1(k4_subset_1(k1_zfmisc_1(X5),X6,X4),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))
      | r2_hidden(X5,k4_subset_1(k1_zfmisc_1(X5),X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:32:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.42  % (15893)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.13/0.42  % (15893)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.43  % (15901)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f118,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ~r2_hidden(sK0,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f52,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    v3_setfam_1(sK2,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK2,sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))),
% 0.20/0.43    inference(flattening,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.43  fof(f12,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.20/0.43    inference(negated_conjecture,[],[f11])).
% 0.20/0.43  fof(f11,conjecture,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ~v3_setfam_1(sK2,sK0) | ~r2_hidden(sK0,sK2)),
% 0.20/0.43    inference(resolution,[],[f39,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.43    inference(nnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    r2_hidden(sK0,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f117,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ~r2_hidden(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f51,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    v3_setfam_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ~v3_setfam_1(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.20/0.43    inference(resolution,[],[f39,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK2)),
% 0.20/0.43    inference(resolution,[],[f110,f80])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.20/0.43    inference(resolution,[],[f59,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r2_hidden(X2,k4_xboole_0(X3,X4)) | r2_hidden(X2,X3)) )),
% 0.20/0.43    inference(resolution,[],[f38,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f33,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  % (15900)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X1,X0)) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(superposition,[],[f43,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.43    inference(nnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.43    inference(subsumption_resolution,[],[f109,f29])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f106,f31])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(superposition,[],[f104,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2))),
% 0.20/0.43    inference(subsumption_resolution,[],[f103,f31])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f100,f29])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.43    inference(resolution,[],[f72,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X6,X4,X5] : (v3_setfam_1(k4_subset_1(k1_zfmisc_1(X5),X6,X4),X5) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) | r2_hidden(X5,k4_subset_1(k1_zfmisc_1(X5),X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5)))) )),
% 0.20/0.43    inference(resolution,[],[f41,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(flattening,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (15893)------------------------------
% 0.20/0.43  % (15893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (15893)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (15893)Memory used [KB]: 1663
% 0.20/0.43  % (15893)Time elapsed: 0.035 s
% 0.20/0.43  % (15893)------------------------------
% 0.20/0.43  % (15893)------------------------------
% 0.20/0.43  % (15887)Success in time 0.082 s
%------------------------------------------------------------------------------
