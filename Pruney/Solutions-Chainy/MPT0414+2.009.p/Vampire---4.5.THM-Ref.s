%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:19 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 933 expanded)
%              Number of leaves         :   16 ( 250 expanded)
%              Depth                    :   24
%              Number of atoms          :  294 (4897 expanded)
%              Number of equality atoms :   38 ( 580 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(subsumption_resolution,[],[f434,f299])).

fof(f299,plain,(
    k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f46,f292])).

fof(f292,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f290,f181])).

fof(f181,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f164,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f164,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f161,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f161,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(sK3(sK2),sK2) ) ),
    inference(resolution,[],[f156,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(X7,sK1) ) ),
    inference(resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

% (15454)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f44,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f290,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f283,f222])).

fof(f222,plain,(
    ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f217,f46])).

fof(f217,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(resolution,[],[f206,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f206,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f201,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f201,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f200,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (15436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (15440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (15447)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (15457)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (15450)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (15465)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

% (15461)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (15458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f200,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f158,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f158,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK6(X9,sK2),sK1)
      | r1_tarski(X9,sK2) ) ),
    inference(resolution,[],[f151,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f283,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f277,f223])).

fof(f223,plain,
    ( r2_hidden(sK5(sK2,sK1),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f221,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

% (15456)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f221,plain,(
    m1_subset_1(sK5(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f216,f46])).

fof(f216,plain,
    ( sK1 = sK2
    | m1_subset_1(sK5(sK2,sK1),sK2) ),
    inference(resolution,[],[f206,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK5(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f277,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f45,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f43,f61])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f434,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f403,f428])).

fof(f428,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f340,f290])).

fof(f340,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | ~ v1_xboole_0(sK2) ) ),
    inference(backward_demodulation,[],[f156,f292])).

fof(f403,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f285,f292])).

fof(f285,plain,
    ( r2_hidden(sK4(sK2),sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f277,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:59:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (15439)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.54  % (15445)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.54  % (15446)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (15459)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (15451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (15446)Refutation not found, incomplete strategy% (15446)------------------------------
% 1.36/0.55  % (15446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (15442)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.55  % (15441)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.56  % (15438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.56  % (15446)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (15446)Memory used [KB]: 10746
% 1.36/0.56  % (15446)Time elapsed: 0.126 s
% 1.36/0.56  % (15446)------------------------------
% 1.36/0.56  % (15446)------------------------------
% 1.36/0.56  % (15443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.56  % (15438)Refutation not found, incomplete strategy% (15438)------------------------------
% 1.52/0.56  % (15438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (15438)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (15438)Memory used [KB]: 10746
% 1.52/0.56  % (15438)Time elapsed: 0.132 s
% 1.52/0.56  % (15438)------------------------------
% 1.52/0.56  % (15438)------------------------------
% 1.52/0.56  % (15437)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  % (15459)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f435,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(subsumption_resolution,[],[f434,f299])).
% 1.52/0.57  fof(f299,plain,(
% 1.52/0.57    k1_xboole_0 != sK2),
% 1.52/0.57    inference(backward_demodulation,[],[f46,f292])).
% 1.52/0.57  fof(f292,plain,(
% 1.52/0.57    k1_xboole_0 = sK1),
% 1.52/0.57    inference(resolution,[],[f290,f181])).
% 1.52/0.57  fof(f181,plain,(
% 1.52/0.57    ~v1_xboole_0(sK2) | k1_xboole_0 = sK1),
% 1.52/0.57    inference(resolution,[],[f164,f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(rectify,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(nnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.57  fof(f164,plain,(
% 1.52/0.57    r2_hidden(sK3(sK2),sK2) | k1_xboole_0 = sK1),
% 1.52/0.57    inference(resolution,[],[f161,f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.52/0.57    inference(ennf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.52/0.57  fof(f161,plain,(
% 1.52/0.57    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(sK3(sK2),sK2)) )),
% 1.52/0.57    inference(resolution,[],[f156,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f156,plain,(
% 1.52/0.57    ( ! [X7] : (~v1_xboole_0(sK2) | ~r2_hidden(X7,sK1)) )),
% 1.52/0.57    inference(resolution,[],[f151,f47])).
% 1.52/0.57  fof(f151,plain,(
% 1.52/0.57    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f145])).
% 1.52/0.57  fof(f145,plain,(
% 1.52/0.57    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 1.52/0.57    inference(resolution,[],[f44,f64])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.52/0.57    inference(resolution,[],[f42,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(flattening,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.52/0.57    inference(nnf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.52/0.57    inference(flattening,[],[f11])).
% 1.52/0.57  fof(f11,plain,(
% 1.52/0.57    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.52/0.57    inference(negated_conjecture,[],[f9])).
% 1.52/0.57  % (15454)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.57  fof(f9,conjecture,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f290,plain,(
% 1.52/0.57    v1_xboole_0(sK2)),
% 1.52/0.57    inference(subsumption_resolution,[],[f283,f222])).
% 1.52/0.57  fof(f222,plain,(
% 1.52/0.57    ~r2_hidden(sK5(sK2,sK1),sK1)),
% 1.52/0.57    inference(subsumption_resolution,[],[f217,f46])).
% 1.52/0.57  fof(f217,plain,(
% 1.52/0.57    sK1 = sK2 | ~r2_hidden(sK5(sK2,sK1),sK1)),
% 1.52/0.57    inference(resolution,[],[f206,f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK5(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(flattening,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.52/0.57  fof(f206,plain,(
% 1.52/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 1.52/0.57    inference(resolution,[],[f201,f50])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.52/0.57  fof(f201,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_zfmisc_1(sK2))),
% 1.52/0.57    inference(resolution,[],[f200,f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f58])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  % (15436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.57  % (15440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.58  % (15447)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.58  % (15457)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.58  % (15450)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.58  % (15465)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.58  fof(f39,plain,(
% 1.52/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.58    inference(rectify,[],[f38])).
% 1.52/0.59  % (15461)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.59  % (15458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.59  fof(f38,plain,(
% 1.52/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.52/0.59    inference(nnf_transformation,[],[f4])).
% 1.52/0.59  fof(f4,axiom,(
% 1.52/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.52/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.52/0.59  fof(f200,plain,(
% 1.52/0.59    r1_tarski(sK1,sK2)),
% 1.52/0.59    inference(duplicate_literal_removal,[],[f197])).
% 1.52/0.59  fof(f197,plain,(
% 1.52/0.59    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 1.52/0.59    inference(resolution,[],[f158,f55])).
% 1.52/0.59  fof(f55,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f37])).
% 1.52/0.59  fof(f37,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.52/0.59  fof(f36,plain,(
% 1.52/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f35,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(rectify,[],[f34])).
% 1.52/0.59  fof(f34,plain,(
% 1.52/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.59    inference(nnf_transformation,[],[f19])).
% 1.52/0.59  fof(f19,plain,(
% 1.52/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.59    inference(ennf_transformation,[],[f2])).
% 1.52/0.59  fof(f2,axiom,(
% 1.52/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.59  fof(f158,plain,(
% 1.52/0.59    ( ! [X9] : (~r2_hidden(sK6(X9,sK2),sK1) | r1_tarski(X9,sK2)) )),
% 1.52/0.59    inference(resolution,[],[f151,f56])).
% 1.52/0.59  fof(f56,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f37])).
% 1.52/0.59  fof(f283,plain,(
% 1.52/0.59    r2_hidden(sK5(sK2,sK1),sK1) | v1_xboole_0(sK2)),
% 1.52/0.59    inference(resolution,[],[f277,f223])).
% 1.52/0.59  fof(f223,plain,(
% 1.52/0.59    r2_hidden(sK5(sK2,sK1),sK2) | v1_xboole_0(sK2)),
% 1.52/0.59    inference(resolution,[],[f221,f51])).
% 1.52/0.59  fof(f51,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f16])).
% 1.52/0.59  % (15456)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.59  fof(f16,plain,(
% 1.52/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.52/0.59    inference(flattening,[],[f15])).
% 1.52/0.59  fof(f15,plain,(
% 1.52/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.52/0.59    inference(ennf_transformation,[],[f7])).
% 1.52/0.59  fof(f7,axiom,(
% 1.52/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.52/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.52/0.59  fof(f221,plain,(
% 1.52/0.59    m1_subset_1(sK5(sK2,sK1),sK2)),
% 1.52/0.59    inference(subsumption_resolution,[],[f216,f46])).
% 1.52/0.59  fof(f216,plain,(
% 1.52/0.59    sK1 = sK2 | m1_subset_1(sK5(sK2,sK1),sK2)),
% 1.52/0.59    inference(resolution,[],[f206,f52])).
% 1.52/0.59  fof(f52,plain,(
% 1.52/0.59    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK5(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f33])).
% 1.52/0.59  fof(f277,plain,(
% 1.52/0.59    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1)) )),
% 1.52/0.59    inference(duplicate_literal_removal,[],[f270])).
% 1.52/0.59  fof(f270,plain,(
% 1.52/0.59    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) )),
% 1.52/0.59    inference(resolution,[],[f45,f72])).
% 1.52/0.59  fof(f72,plain,(
% 1.52/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 1.52/0.59    inference(resolution,[],[f43,f61])).
% 1.52/0.59  fof(f43,plain,(
% 1.52/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.52/0.59    inference(cnf_transformation,[],[f25])).
% 1.52/0.59  fof(f45,plain,(
% 1.52/0.59    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f25])).
% 1.52/0.59  fof(f46,plain,(
% 1.52/0.59    sK1 != sK2),
% 1.52/0.59    inference(cnf_transformation,[],[f25])).
% 1.52/0.59  fof(f434,plain,(
% 1.52/0.59    k1_xboole_0 = sK2),
% 1.52/0.59    inference(subsumption_resolution,[],[f403,f428])).
% 1.52/0.59  fof(f428,plain,(
% 1.52/0.59    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) )),
% 1.52/0.59    inference(subsumption_resolution,[],[f340,f290])).
% 1.52/0.59  fof(f340,plain,(
% 1.52/0.59    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0) | ~v1_xboole_0(sK2)) )),
% 1.52/0.59    inference(backward_demodulation,[],[f156,f292])).
% 1.52/0.59  fof(f403,plain,(
% 1.52/0.59    r2_hidden(sK4(sK2),k1_xboole_0) | k1_xboole_0 = sK2),
% 1.52/0.59    inference(backward_demodulation,[],[f285,f292])).
% 1.52/0.59  fof(f285,plain,(
% 1.52/0.59    r2_hidden(sK4(sK2),sK1) | k1_xboole_0 = sK2),
% 1.52/0.59    inference(resolution,[],[f277,f49])).
% 1.52/0.59  % SZS output end Proof for theBenchmark
% 1.52/0.59  % (15459)------------------------------
% 1.52/0.59  % (15459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (15459)Termination reason: Refutation
% 1.52/0.59  
% 1.52/0.59  % (15459)Memory used [KB]: 1918
% 1.52/0.59  % (15459)Time elapsed: 0.114 s
% 1.52/0.59  % (15459)------------------------------
% 1.52/0.59  % (15459)------------------------------
% 1.52/0.59  % (15435)Success in time 0.227 s
%------------------------------------------------------------------------------
