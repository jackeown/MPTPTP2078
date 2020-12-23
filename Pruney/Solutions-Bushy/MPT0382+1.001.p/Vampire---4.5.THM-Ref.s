%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0382+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  64 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   75 ( 204 expanded)
%              Number of equality atoms :   24 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f22,f17,f178,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ3_eqProxy(k3_subset_1(X0,X2),k3_subset_1(X1,X3))
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f178,plain,(
    ~ sQ3_eqProxy(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f75,f10])).

fof(f10,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ) ),
    inference(resolution,[],[f73,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(X0,sK1)
      | ~ sQ3_eqProxy(X0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ) ),
    inference(resolution,[],[f45,f11])).

fof(f11,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ sQ3_eqProxy(X0,k3_subset_1(X1,k3_subset_1(X1,sK2)))
      | ~ sQ3_eqProxy(X0,sK1) ) ),
    inference(resolution,[],[f37,f18])).

fof(f37,plain,(
    ! [X2,X1] :
      ( ~ sQ3_eqProxy(X2,sK2)
      | ~ sQ3_eqProxy(X1,sK1)
      | ~ sQ3_eqProxy(X1,X2) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

% (1090)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f31,plain,(
    ! [X2] :
      ( ~ sQ3_eqProxy(X2,sK2)
      | ~ sQ3_eqProxy(X2,sK1) ) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(sK1,X0)
      | ~ sQ3_eqProxy(X0,sK2) ) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    ~ sQ3_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f13,f15])).

fof(f13,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    sQ3_eqProxy(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f12,f15])).

fof(f12,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f15])).

%------------------------------------------------------------------------------
