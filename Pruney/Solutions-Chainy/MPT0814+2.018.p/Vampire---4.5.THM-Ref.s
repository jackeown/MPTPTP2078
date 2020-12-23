%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 103 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 405 expanded)
%              Number of equality atoms :   15 (  68 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f77,f81])).

fof(f81,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    r2_hidden(sK4(sK1,sK2,sK0),sK1) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f13,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).

fof(f8,plain,
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

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK4(X0,X1,sK0),X0) ) ),
    inference(resolution,[],[f14,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f7,f11])).

fof(f11,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f14,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,
    ( ~ r2_hidden(sK4(sK1,sK2,sK0),sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r2_hidden(sK4(sK1,sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f77,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    r2_hidden(sK5(sK1,sK2,sK0),sK2) ),
    inference(resolution,[],[f26,f28])).

fof(f26,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK5(X2,X3,sK0),X3) ) ),
    inference(resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK0),sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> r2_hidden(sK5(sK1,sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f74,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f68,f14])).

fof(f68,plain,
    ( ~ r2_hidden(sK0,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_3
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f69,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f56,f66,f62,f58])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(sK4(sK1,sK2,sK0),sK1)
    | ~ r2_hidden(sK5(sK1,sK2,sK0),sK2) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    ! [X4,X5] :
      ( ~ sQ6_eqProxy(k4_tarski(X4,X5),sK0)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(equality_proxy_replacement,[],[f15,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f15,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1)
      | k4_tarski(X4,X5) != sK0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2] :
      ( sQ6_eqProxy(k4_tarski(sK4(sK1,sK2,X2),sK5(sK1,sK2,X2)),X2)
      | ~ r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ6_eqProxy(k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)),X3)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f20,f21])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5955)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (5955)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (5963)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f69,f74,f77,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    $false | spl7_2),
% 0.20/0.47    inference(resolution,[],[f64,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    r2_hidden(sK4(sK1,sK2,sK0),sK1)),
% 0.20/0.47    inference(resolution,[],[f25,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.47    inference(resolution,[],[f13,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.47    inference(flattening,[],[f5])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(sK3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK4(X0,X1,sK0),X0)) )),
% 0.20/0.47    inference(resolution,[],[f14,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f7,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    r2_hidden(sK0,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK1,sK2,sK0),sK1) | spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl7_2 <=> r2_hidden(sK4(sK1,sK2,sK0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl7_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    $false | spl7_1),
% 0.20/0.47    inference(resolution,[],[f60,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r2_hidden(sK5(sK1,sK2,sK0),sK2)),
% 0.20/0.47    inference(resolution,[],[f26,f28])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~r1_tarski(sK3,k2_zfmisc_1(X2,X3)) | r2_hidden(sK5(X2,X3,sK0),X3)) )),
% 0.20/0.47    inference(resolution,[],[f14,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~r2_hidden(sK5(sK1,sK2,sK0),sK2) | spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl7_1 <=> r2_hidden(sK5(sK1,sK2,sK0),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    $false | spl7_3),
% 0.20/0.47    inference(resolution,[],[f68,f14])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~r2_hidden(sK0,sK3) | spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl7_3 <=> r2_hidden(sK0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f56,f66,f62,f58])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~r2_hidden(sK0,sK3) | ~r2_hidden(sK4(sK1,sK2,sK0),sK1) | ~r2_hidden(sK5(sK1,sK2,sK0),sK2)),
% 0.20/0.47    inference(resolution,[],[f32,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X4,X5] : (~sQ6_eqProxy(k4_tarski(X4,X5),sK0) | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f15,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2] : (sQ6_eqProxy(k4_tarski(sK4(sK1,sK2,X2),sK5(sK1,sK2,X2)),X2) | ~r2_hidden(X2,sK3)) )),
% 0.20/0.47    inference(resolution,[],[f28,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (sQ6_eqProxy(k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)),X3) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f20,f21])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (5955)------------------------------
% 0.20/0.47  % (5955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5955)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (5955)Memory used [KB]: 6140
% 0.20/0.47  % (5955)Time elapsed: 0.054 s
% 0.20/0.47  % (5955)------------------------------
% 0.20/0.47  % (5955)------------------------------
% 0.20/0.48  % (5942)Success in time 0.119 s
%------------------------------------------------------------------------------
