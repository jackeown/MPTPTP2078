%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 255 expanded)
%              Number of leaves         :    5 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 (1872 expanded)
%              Number of equality atoms :   22 ( 262 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f52])).

fof(f52,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f49,f18])).

fof(f18,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) )
          & ( r2_hidden(X3,sK2)
            | r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & ! [X3] :
          ( ( ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) )
            & ( r2_hidden(X3,sK2)
              | r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).

fof(f49,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f48,f30])).

fof(f48,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f43,f20])).

fof(f20,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f29,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,X2,sK2),X2)
      | k3_subset_1(sK0,sK2) = X2
      | r2_hidden(sK3(sK0,X2,sK2),sK2) ) ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f16,f17,f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | k3_subset_1(X0,X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f16,f17,f20,f49,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:30:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27929)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (27934)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (27941)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (27941)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f30,f49,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X3] : (r2_hidden(X3,sK2) | r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f4])).
% 0.21/0.48  fof(f4,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f2])).
% 0.21/0.48  fof(f2,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f30])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.48    inference(resolution,[],[f45,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    sK1 != k3_subset_1(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2) | r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.21/0.48    inference(resolution,[],[f29,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,X2,sK2),X2) | k3_subset_1(sK0,sK2) = X2 | r2_hidden(sK3(sK0,X2,sK2),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f17,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | k3_subset_1(X0,X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ((r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (~r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (~r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (~r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : ((r2_hidden(X3,X1) <~> ~r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k3_subset_1(X0,X2) = X1 | ? [X3] : ((r2_hidden(X3,X1) <~> ~r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f17,f20,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | k3_subset_1(X0,X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f16,f17,f20,f49,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_subset_1(X0,X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27941)------------------------------
% 0.21/0.48  % (27941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27941)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27941)Memory used [KB]: 6140
% 0.21/0.48  % (27941)Time elapsed: 0.007 s
% 0.21/0.48  % (27941)------------------------------
% 0.21/0.48  % (27941)------------------------------
% 0.21/0.49  % (27925)Success in time 0.122 s
%------------------------------------------------------------------------------
