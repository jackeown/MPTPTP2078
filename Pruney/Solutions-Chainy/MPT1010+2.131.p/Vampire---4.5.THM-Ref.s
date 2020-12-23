%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:09 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 459 expanded)
%              Number of equality atoms :  114 ( 223 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f74,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f51,f64])).

fof(f64,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f63,f26])).

fof(f26,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f63,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | sK1 = k1_funct_1(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | sK1 = k1_funct_1(sK3,sK2)
    | sK1 = k1_funct_1(sK3,sK2)
    | sK1 = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f60,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f59,f25])).

fof(f25,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f58,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
      | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X2,X0)
      | r2_hidden(k1_funct_1(sK3,X1),X0) ) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f51,plain,(
    ! [X2,X0,X1] : ~ r1_tarski(k1_enumset1(X0,X1,X2),X2) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f44,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (787283969)
% 0.21/0.38  ipcrm: permission denied for id (787349509)
% 0.21/0.38  ipcrm: permission denied for id (787382279)
% 0.21/0.38  ipcrm: permission denied for id (787480588)
% 0.21/0.39  ipcrm: permission denied for id (787546130)
% 0.22/0.44  ipcrm: permission denied for id (787677239)
% 0.22/0.44  ipcrm: permission denied for id (787710008)
% 0.22/0.44  ipcrm: permission denied for id (787742778)
% 0.22/0.45  ipcrm: permission denied for id (787775551)
% 0.22/0.45  ipcrm: permission denied for id (787808321)
% 0.22/0.46  ipcrm: permission denied for id (787841093)
% 0.22/0.49  ipcrm: permission denied for id (788004957)
% 0.22/0.51  ipcrm: permission denied for id (788070506)
% 0.22/0.51  ipcrm: permission denied for id (788103281)
% 0.22/0.53  ipcrm: permission denied for id (788267131)
% 1.10/0.66  % (22486)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.10/0.66  % (22481)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.10/0.67  % (22501)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.10/0.68  % (22485)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.10/0.68  % (22507)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.10/0.68  % (22486)Refutation found. Thanks to Tanya!
% 1.10/0.68  % SZS status Theorem for theBenchmark
% 1.10/0.68  % SZS output start Proof for theBenchmark
% 1.10/0.68  fof(f78,plain,(
% 1.10/0.68    $false),
% 1.10/0.68    inference(subsumption_resolution,[],[f74,f39])).
% 1.10/0.68  fof(f39,plain,(
% 1.10/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.10/0.68    inference(cnf_transformation,[],[f1])).
% 1.10/0.68  fof(f1,axiom,(
% 1.10/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.10/0.68  fof(f74,plain,(
% 1.10/0.68    ~r1_tarski(k1_xboole_0,sK1)),
% 1.10/0.68    inference(superposition,[],[f51,f64])).
% 1.10/0.68  fof(f64,plain,(
% 1.10/0.68    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.10/0.68    inference(subsumption_resolution,[],[f63,f26])).
% 1.10/0.68  fof(f26,plain,(
% 1.10/0.68    sK1 != k1_funct_1(sK3,sK2)),
% 1.10/0.68    inference(cnf_transformation,[],[f16])).
% 1.10/0.68  fof(f16,plain,(
% 1.10/0.68    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.10/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f15])).
% 1.10/0.68  fof(f15,plain,(
% 1.10/0.68    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.10/0.68    introduced(choice_axiom,[])).
% 1.10/0.68  fof(f10,plain,(
% 1.10/0.68    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.10/0.68    inference(flattening,[],[f9])).
% 1.10/0.68  fof(f9,plain,(
% 1.10/0.68    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.10/0.68    inference(ennf_transformation,[],[f8])).
% 1.10/0.68  fof(f8,negated_conjecture,(
% 1.10/0.68    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.10/0.68    inference(negated_conjecture,[],[f7])).
% 1.10/0.68  fof(f7,conjecture,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.10/0.68  fof(f63,plain,(
% 1.10/0.68    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK1 = k1_funct_1(sK3,sK2)),
% 1.10/0.68    inference(duplicate_literal_removal,[],[f61])).
% 1.10/0.68  fof(f61,plain,(
% 1.10/0.68    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK1 = k1_funct_1(sK3,sK2) | sK1 = k1_funct_1(sK3,sK2) | sK1 = k1_funct_1(sK3,sK2)),
% 1.10/0.68    inference(resolution,[],[f60,f49])).
% 1.10/0.68  fof(f49,plain,(
% 1.10/0.68    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.10/0.68    inference(equality_resolution,[],[f27])).
% 1.10/0.68  fof(f27,plain,(
% 1.10/0.68    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.10/0.68    inference(cnf_transformation,[],[f21])).
% 1.10/0.68  fof(f21,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.10/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.10/0.68  fof(f20,plain,(
% 1.10/0.68    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.10/0.68    introduced(choice_axiom,[])).
% 1.10/0.68  fof(f19,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.10/0.68    inference(rectify,[],[f18])).
% 1.10/0.68  fof(f18,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.10/0.68    inference(flattening,[],[f17])).
% 1.10/0.68  fof(f17,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.10/0.68    inference(nnf_transformation,[],[f11])).
% 1.10/0.68  fof(f11,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.10/0.68    inference(ennf_transformation,[],[f2])).
% 1.10/0.68  fof(f2,axiom,(
% 1.10/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.10/0.68  fof(f60,plain,(
% 1.10/0.68    r2_hidden(k1_funct_1(sK3,sK2),k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.10/0.68    inference(resolution,[],[f59,f25])).
% 1.10/0.68  fof(f25,plain,(
% 1.10/0.68    r2_hidden(sK2,sK0)),
% 1.10/0.68    inference(cnf_transformation,[],[f16])).
% 1.10/0.68  fof(f59,plain,(
% 1.10/0.68    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))) )),
% 1.10/0.68    inference(subsumption_resolution,[],[f58,f42])).
% 1.10/0.68  fof(f42,plain,(
% 1.10/0.68    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 1.10/0.68    inference(definition_unfolding,[],[f23,f40])).
% 1.10/0.68  fof(f40,plain,(
% 1.10/0.68    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.10/0.68    inference(definition_unfolding,[],[f37,f36])).
% 1.10/0.68  fof(f36,plain,(
% 1.10/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.10/0.68    inference(cnf_transformation,[],[f4])).
% 1.10/0.68  fof(f4,axiom,(
% 1.10/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.10/0.68  fof(f37,plain,(
% 1.10/0.68    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.10/0.68    inference(cnf_transformation,[],[f3])).
% 1.10/0.68  fof(f3,axiom,(
% 1.10/0.68    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.10/0.68  fof(f23,plain,(
% 1.10/0.68    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.10/0.68    inference(cnf_transformation,[],[f16])).
% 1.10/0.68  fof(f58,plain,(
% 1.10/0.68    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))) )),
% 1.10/0.68    inference(resolution,[],[f57,f41])).
% 1.10/0.68  fof(f41,plain,(
% 1.10/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 1.10/0.68    inference(definition_unfolding,[],[f24,f40])).
% 1.10/0.68  fof(f24,plain,(
% 1.10/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.10/0.68    inference(cnf_transformation,[],[f16])).
% 1.10/0.68  fof(f57,plain,(
% 1.10/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X2,X0) | r2_hidden(k1_funct_1(sK3,X1),X0)) )),
% 1.10/0.68    inference(resolution,[],[f35,f22])).
% 1.10/0.68  fof(f22,plain,(
% 1.10/0.68    v1_funct_1(sK3)),
% 1.10/0.68    inference(cnf_transformation,[],[f16])).
% 1.10/0.68  fof(f35,plain,(
% 1.10/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.10/0.68    inference(cnf_transformation,[],[f13])).
% 1.10/0.68  fof(f13,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.10/0.68    inference(flattening,[],[f12])).
% 1.10/0.68  fof(f12,plain,(
% 1.10/0.68    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.10/0.68    inference(ennf_transformation,[],[f6])).
% 1.10/0.68  fof(f6,axiom,(
% 1.10/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.10/0.68  fof(f51,plain,(
% 1.10/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X1,X2),X2)) )),
% 1.10/0.68    inference(resolution,[],[f44,f38])).
% 1.10/0.68  fof(f38,plain,(
% 1.10/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.10/0.68    inference(cnf_transformation,[],[f14])).
% 1.10/0.68  fof(f14,plain,(
% 1.10/0.68    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.10/0.68    inference(ennf_transformation,[],[f5])).
% 1.10/0.68  fof(f5,axiom,(
% 1.10/0.68    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.10/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.10/0.68  fof(f44,plain,(
% 1.10/0.68    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.10/0.68    inference(equality_resolution,[],[f43])).
% 1.10/0.68  fof(f43,plain,(
% 1.10/0.68    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.10/0.68    inference(equality_resolution,[],[f30])).
% 1.10/0.68  fof(f30,plain,(
% 1.10/0.68    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.10/0.68    inference(cnf_transformation,[],[f21])).
% 1.10/0.68  % SZS output end Proof for theBenchmark
% 1.10/0.68  % (22486)------------------------------
% 1.10/0.68  % (22486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.68  % (22486)Termination reason: Refutation
% 1.10/0.68  
% 1.10/0.68  % (22486)Memory used [KB]: 6268
% 1.10/0.68  % (22486)Time elapsed: 0.104 s
% 1.10/0.68  % (22486)------------------------------
% 1.10/0.68  % (22486)------------------------------
% 1.10/0.68  % (22508)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.10/0.68  % (22484)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.10/0.68  % (22256)Success in time 0.319 s
%------------------------------------------------------------------------------
