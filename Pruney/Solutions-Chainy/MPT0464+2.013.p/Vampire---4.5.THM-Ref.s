%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 145 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  285 ( 800 expanded)
%              Number of equality atoms :   29 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f349,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f349,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f340,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k3_xboole_0(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f340,plain,(
    ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f309,f137])).

fof(f137,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f136,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f136,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f135,f34])).

fof(f135,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f133,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f105,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

% (29347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (29332)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (29348)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (29345)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (29352)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (29341)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (29341)Refutation not found, incomplete strategy% (29341)------------------------------
% (29341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29341)Termination reason: Refutation not found, incomplete strategy

% (29341)Memory used [KB]: 1663
% (29341)Time elapsed: 0.103 s
% (29341)------------------------------
% (29341)------------------------------
% (29340)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (29343)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (29343)Refutation not found, incomplete strategy% (29343)------------------------------
% (29343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29343)Termination reason: Refutation not found, incomplete strategy

% (29343)Memory used [KB]: 10618
% (29343)Time elapsed: 0.136 s
% (29343)------------------------------
% (29343)------------------------------
% (29339)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (29342)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (29344)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (29328)Refutation not found, incomplete strategy% (29328)------------------------------
% (29328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29328)Termination reason: Refutation not found, incomplete strategy

% (29328)Memory used [KB]: 1791
% (29328)Time elapsed: 0.127 s
% (29328)------------------------------
% (29328)------------------------------
fof(f105,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f104,f33])).

fof(f104,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f309,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f39,f268])).

fof(f268,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))
      | k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f173,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f141,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f141,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK3(X0,X1,X1),X1)
      | ~ r2_hidden(sK3(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK3(X0,X1,X1),X1)
      | ~ r2_hidden(sK3(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X0)),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X0) ) ),
    inference(factoring,[],[f87])).

fof(f87,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X7)
      | k3_xboole_0(X6,X7) = k3_xboole_0(X4,X5)
      | r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (29329)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (29351)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (29338)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (29335)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (29334)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (29353)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (29353)Refutation not found, incomplete strategy% (29353)------------------------------
% 0.22/0.53  % (29353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29353)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29353)Memory used [KB]: 6140
% 0.22/0.53  % (29353)Time elapsed: 0.114 s
% 0.22/0.53  % (29353)------------------------------
% 0.22/0.53  % (29353)------------------------------
% 0.22/0.53  % (29331)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (29330)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (29350)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (29351)Refutation not found, incomplete strategy% (29351)------------------------------
% 0.22/0.54  % (29351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29351)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29351)Memory used [KB]: 10746
% 0.22/0.54  % (29351)Time elapsed: 0.121 s
% 0.22/0.54  % (29351)------------------------------
% 0.22/0.54  % (29351)------------------------------
% 0.22/0.54  % (29327)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (29328)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (29337)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (29336)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (29356)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (29355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (29356)Refutation not found, incomplete strategy% (29356)------------------------------
% 0.22/0.55  % (29356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29356)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29356)Memory used [KB]: 1791
% 0.22/0.55  % (29356)Time elapsed: 0.139 s
% 0.22/0.55  % (29356)------------------------------
% 0.22/0.55  % (29356)------------------------------
% 0.22/0.55  % (29333)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (29336)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f349,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v1_relat_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f13])).
% 0.22/0.55  fof(f13,conjecture,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    ~v1_relat_1(sK1)),
% 0.22/0.55    inference(resolution,[],[f340,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X1] : (v1_relat_1(k3_xboole_0(X1,X2)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(resolution,[],[f63,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f38,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f340,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 0.22/0.55    inference(resolution,[],[f309,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f136,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    v1_relat_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f135,f34])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f134,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f39])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(resolution,[],[f105,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.22/0.55  % (29347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (29332)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (29348)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (29345)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (29352)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (29341)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (29341)Refutation not found, incomplete strategy% (29341)------------------------------
% 0.22/0.55  % (29341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29341)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29341)Memory used [KB]: 1663
% 0.22/0.55  % (29341)Time elapsed: 0.103 s
% 0.22/0.55  % (29341)------------------------------
% 0.22/0.55  % (29341)------------------------------
% 0.22/0.56  % (29340)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (29343)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (29343)Refutation not found, incomplete strategy% (29343)------------------------------
% 0.22/0.56  % (29343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29343)Memory used [KB]: 10618
% 0.22/0.56  % (29343)Time elapsed: 0.136 s
% 0.22/0.56  % (29343)------------------------------
% 0.22/0.56  % (29343)------------------------------
% 0.22/0.56  % (29339)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (29342)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (29344)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (29328)Refutation not found, incomplete strategy% (29328)------------------------------
% 0.22/0.56  % (29328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29328)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29328)Memory used [KB]: 1791
% 0.22/0.56  % (29328)Time elapsed: 0.127 s
% 0.22/0.56  % (29328)------------------------------
% 0.22/0.56  % (29328)------------------------------
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f104,f33])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f103,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f102,f57])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f37,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f48,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.56  fof(f309,plain,(
% 0.22/0.56    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.22/0.56    inference(superposition,[],[f39,f268])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f261])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) | k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.22/0.56    inference(resolution,[],[f173,f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f141,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(factoring,[],[f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(rectify,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(flattening,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK3(X0,X1,X1),X1) | ~r2_hidden(sK3(X0,X1,X1),X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK3(X0,X1,X1),X1) | ~r2_hidden(sK3(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(resolution,[],[f93,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X0)),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X0)) )),
% 0.22/0.56    inference(factoring,[],[f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X7) | k3_xboole_0(X6,X7) = k3_xboole_0(X4,X5) | r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X4)) )),
% 0.22/0.56    inference(resolution,[],[f52,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (29336)------------------------------
% 0.22/0.57  % (29336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (29336)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (29336)Memory used [KB]: 1918
% 0.22/0.57  % (29336)Time elapsed: 0.130 s
% 0.22/0.57  % (29336)------------------------------
% 0.22/0.57  % (29336)------------------------------
% 0.22/0.57  % (29326)Success in time 0.203 s
%------------------------------------------------------------------------------
