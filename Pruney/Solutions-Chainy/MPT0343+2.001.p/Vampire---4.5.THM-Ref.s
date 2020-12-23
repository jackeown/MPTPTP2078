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
% DateTime   : Thu Dec  3 12:43:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 136 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  197 ( 625 expanded)
%              Number of equality atoms :   20 (  63 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f107,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f90,f106])).

fof(f106,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f105,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f105,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f103,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK2),sK1)
      | ~ r2_hidden(sK4(X0,sK2),sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f29,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f89,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f89,plain,(
    sK2 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f88,f39])).

fof(f88,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f75,f41])).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | r2_hidden(sK4(sK2,X0),sK1)
      | ~ r2_hidden(sK4(sK2,X0),sK2) ) ),
    inference(resolution,[],[f62,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f30,f43])).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1),sK0)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f56,f41])).

% (19436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f56,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (19437)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (19429)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (19421)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (19418)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (19421)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (19414)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f107,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    sK1 != sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    sK1 = sK2),
% 0.20/0.52    inference(backward_demodulation,[],[f90,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    sK1 = k3_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f105,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f103,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f55,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f40,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ~r2_hidden(sK4(sK1,sK2),sK0) | r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ~r2_hidden(sK4(sK1,sK2),sK0) | r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f52,f41])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4(X0,sK2),sK1) | ~r2_hidden(sK4(X0,sK2),sK0) | r1_tarski(X0,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f50,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f29,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f36,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(rectify,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    sK2 = k3_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(superposition,[],[f89,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    sK2 = k3_xboole_0(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f88,f39])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    r1_tarski(sK2,sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f77,f42])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f75,f41])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(sK2,X0) | r2_hidden(sK4(sK2,X0),sK1) | ~r2_hidden(sK4(sK2,X0),sK2)) )),
% 0.20/0.52    inference(resolution,[],[f62,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f30,f43])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK0) | r1_tarski(sK2,X1)) )),
% 0.20/0.52    inference(resolution,[],[f56,f41])).
% 0.20/0.53  % (19436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (19421)------------------------------
% 0.20/0.53  % (19421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19421)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (19421)Memory used [KB]: 6268
% 0.20/0.53  % (19421)Time elapsed: 0.078 s
% 0.20/0.53  % (19421)------------------------------
% 0.20/0.53  % (19421)------------------------------
% 0.20/0.53  % (19419)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (19413)Success in time 0.174 s
%------------------------------------------------------------------------------
