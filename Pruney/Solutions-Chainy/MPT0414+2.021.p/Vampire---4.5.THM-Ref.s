%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 265 expanded)
%              Number of leaves         :    5 (  75 expanded)
%              Depth                    :   25
%              Number of atoms          :  192 (1907 expanded)
%              Number of equality atoms :   25 ( 266 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).

fof(f9,plain,
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

fof(f10,plain,
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

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f65,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f64,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f63,f37])).

fof(f37,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f35,f17])).

fof(f35,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f34,f20])).

fof(f20,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
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
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f33,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f28,f20])).

fof(f28,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f24,f17])).

fof(f24,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK1)
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f22,f16])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f61,f20])).

fof(f61,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f23,f42])).

fof(f42,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f41,f16])).

fof(f41,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f40,f17])).

fof(f40,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f39,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f38,f21])).

fof(f38,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.42/0.57  % (3631)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.42/0.57  % (3651)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.42/0.57  % (3650)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.59/0.57  % (3641)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.59/0.57  % (3647)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.59/0.57  % (3640)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.59/0.57  % (3643)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.59/0.57  % (3635)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.59/0.57  % (3630)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.59/0.57  % (3631)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % (3635)Refutation not found, incomplete strategy% (3635)------------------------------
% 1.59/0.57  % (3635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (3635)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (3635)Memory used [KB]: 1535
% 1.59/0.57  % (3635)Time elapsed: 0.132 s
% 1.59/0.57  % (3635)------------------------------
% 1.59/0.57  % (3635)------------------------------
% 1.59/0.57  % (3649)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.59/0.57  % (3642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.59/0.57  % (3632)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.59/0.57  % (3634)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.59/0.58  % (3633)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.59/0.58  % (3639)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.59/0.58  % (3634)Refutation not found, incomplete strategy% (3634)------------------------------
% 1.59/0.58  % (3634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (3648)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.59/0.58  % (3632)Refutation not found, incomplete strategy% (3632)------------------------------
% 1.59/0.58  % (3632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (3632)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (3632)Memory used [KB]: 6140
% 1.59/0.58  % (3632)Time elapsed: 0.139 s
% 1.59/0.58  % (3632)------------------------------
% 1.59/0.58  % (3632)------------------------------
% 1.59/0.58  % (3646)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.59/0.58  % (3638)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.59/0.58  % (3636)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.59/0.59  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f66,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(subsumption_resolution,[],[f65,f16])).
% 1.59/0.59  fof(f16,plain,(
% 1.59/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,plain,(
% 1.59/0.59    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).
% 1.59/0.59  fof(f9,plain,(
% 1.59/0.59    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f10,plain,(
% 1.59/0.59    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f8,plain,(
% 1.59/0.59    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.59    inference(nnf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,plain,(
% 1.59/0.59    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.59    inference(flattening,[],[f4])).
% 1.59/0.59  fof(f4,plain,(
% 1.59/0.59    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.59/0.59    inference(ennf_transformation,[],[f3])).
% 1.59/0.59  fof(f3,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.59/0.59    inference(negated_conjecture,[],[f2])).
% 1.59/0.59  fof(f2,conjecture,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 1.59/0.59  fof(f65,plain,(
% 1.59/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f64,f17])).
% 1.59/0.59  fof(f17,plain,(
% 1.59/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f64,plain,(
% 1.59/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f63,f37])).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)),
% 1.59/0.59    inference(subsumption_resolution,[],[f36,f16])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f35,f17])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f34,f20])).
% 1.59/0.59  fof(f20,plain,(
% 1.59/0.59    sK1 != sK2),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f34,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | sK1 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(resolution,[],[f33,f21])).
% 1.59/0.59  fof(f21,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f15])).
% 1.59/0.59  fof(f15,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 1.59/0.59  fof(f14,plain,(
% 1.59/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f13,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(flattening,[],[f12])).
% 1.59/0.59  fof(f12,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(nnf_transformation,[],[f7])).
% 1.59/0.59  fof(f7,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(flattening,[],[f6])).
% 1.59/0.59  fof(f6,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.59/0.59  fof(f33,plain,(
% 1.59/0.59    ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)),
% 1.59/0.59    inference(duplicate_literal_removal,[],[f32])).
% 1.59/0.59  fof(f32,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))),
% 1.59/0.59    inference(resolution,[],[f31,f19])).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f31,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)),
% 1.59/0.59    inference(subsumption_resolution,[],[f28,f20])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | sK1 = sK2),
% 1.59/0.59    inference(resolution,[],[f24,f17])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),X0) | sK1 = X0) )),
% 1.59/0.59    inference(resolution,[],[f22,f16])).
% 1.59/0.59  fof(f22,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.59/0.59    inference(cnf_transformation,[],[f15])).
% 1.59/0.59  fof(f63,plain,(
% 1.59/0.59    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f61,f20])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    sK1 = sK2 | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(resolution,[],[f23,f42])).
% 1.59/0.59  fof(f42,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 1.59/0.59    inference(subsumption_resolution,[],[f41,f16])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f40,f17])).
% 1.59/0.59  fof(f40,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f39,f20])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | sK1 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.59/0.59    inference(resolution,[],[f38,f21])).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ~m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 1.59/0.59    inference(resolution,[],[f37,f18])).
% 1.59/0.59  fof(f18,plain,(
% 1.59/0.59    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f15])).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (3631)------------------------------
% 1.59/0.59  % (3631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (3631)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (3631)Memory used [KB]: 6140
% 1.59/0.59  % (3634)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (3634)Memory used [KB]: 10618
% 1.59/0.59  % (3634)Time elapsed: 0.142 s
% 1.59/0.59  % (3634)------------------------------
% 1.59/0.59  % (3634)------------------------------
% 1.59/0.59  % (3631)Time elapsed: 0.132 s
% 1.59/0.59  % (3631)------------------------------
% 1.59/0.59  % (3631)------------------------------
% 1.59/0.59  % (3627)Success in time 0.224 s
%------------------------------------------------------------------------------
