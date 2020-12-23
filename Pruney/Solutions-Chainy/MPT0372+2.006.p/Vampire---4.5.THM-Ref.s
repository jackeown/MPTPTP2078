%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 269 expanded)
%              Number of leaves         :    5 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  191 (1919 expanded)
%              Number of equality atoms :   26 ( 270 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f65])).

fof(f65,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f64,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
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

fof(f64,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f62])).

fof(f62,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f61,f56])).

fof(f56,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f45,f18])).

fof(f18,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f44,f16])).

fof(f44,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sK1 != X0
      | m1_subset_1(sK3(sK0,X0,sK2),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f36,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( sK1 != X0
      | m1_subset_1(sK3(sK0,X0,sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & ( r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X1)
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
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

fof(f20,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f60,f16])).

fof(f60,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(sK0,X1,sK2),sK2)
      | ~ r2_hidden(sK3(sK0,X1,sK2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f37,f17])).

fof(f37,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(sK0,X1,sK2),sK2)
      | ~ r2_hidden(sK3(sK0,X1,sK2),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2] :
      ( sK1 != X2
      | ~ r2_hidden(sK3(sK0,X2,sK2),sK2)
      | r2_hidden(sK3(sK0,X2,sK2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f38,plain,(
    ! [X2] :
      ( sK1 != X2
      | ~ r2_hidden(sK3(sK0,X2,sK2),sK2)
      | r2_hidden(sK3(sK0,X2,sK2),X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f55,f62])).

fof(f55,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15919)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15924)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (15933)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (15924)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f64,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10,f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f4])).
% 0.22/0.52  fof(f4,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f2])).
% 0.22/0.52  fof(f2,conjecture,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f63,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK1) | r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.22/0.52    inference(resolution,[],[f45,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f44,f16])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    m1_subset_1(sK3(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(equality_resolution,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 != X0 | m1_subset_1(sK3(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f36,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 != X0 | m1_subset_1(sK3(sK0,X0,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(superposition,[],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_subset_1(X0,X2) = X1 | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ((~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : ((~r2_hidden(X3,X2) | r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : (((~r2_hidden(X3,X2) | r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,X2) = X1 | ? [X3] : ((~r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((k3_subset_1(X0,X2) = X1 | ? [X3] : ((~r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    sK1 != k3_subset_1(sK0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f60,f16])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(equality_resolution,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X1] : (sK1 != X1 | r2_hidden(sK3(sK0,X1,sK2),sK2) | ~r2_hidden(sK3(sK0,X1,sK2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f17])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X1] : (sK1 != X1 | r2_hidden(sK3(sK0,X1,sK2),sK2) | ~r2_hidden(sK3(sK0,X1,sK2),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(superposition,[],[f20,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_subset_1(X0,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1,sK2),sK2) | r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(equality_resolution,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2] : (sK1 != X2 | ~r2_hidden(sK3(sK0,X2,sK2),sK2) | r2_hidden(sK3(sK0,X2,sK2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f38,f17])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2] : (sK1 != X2 | ~r2_hidden(sK3(sK0,X2,sK2),sK2) | r2_hidden(sK3(sK0,X2,sK2),X2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(superposition,[],[f20,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_subset_1(X0,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f55,f62])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f45,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15924)------------------------------
% 0.22/0.52  % (15924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15924)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15924)Memory used [KB]: 1663
% 0.22/0.52  % (15924)Time elapsed: 0.085 s
% 0.22/0.52  % (15924)------------------------------
% 0.22/0.52  % (15924)------------------------------
% 0.22/0.52  % (15915)Success in time 0.158 s
%------------------------------------------------------------------------------
