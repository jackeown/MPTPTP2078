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
% DateTime   : Thu Dec  3 12:57:29 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 268 expanded)
%              Number of leaves         :   16 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  268 (1792 expanded)
%              Number of equality atoms :   13 (  68 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(subsumption_resolution,[],[f416,f234])).

fof(f234,plain,(
    ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK7(sK2,sK3)),k2_zfmisc_1(X1,sK1)) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2) ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f63,plain,(
    r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    inference(backward_demodulation,[],[f38,f56])).

fof(f56,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X5,X3),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X5,X3),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK3),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f38,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK3),sK2)
      | ~ r2_hidden(k4_tarski(X4,X3),k2_zfmisc_1(X5,sK1)) ) ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

% (26761)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (26759)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (26757)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (26756)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f78,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(k4_tarski(X2,sK3),sK2) ) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f64,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(subsumption_resolution,[],[f62,f63])).

fof(f62,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(backward_demodulation,[],[f39,f56])).

fof(f39,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f416,plain,(
    r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(k2_relat_1(sK2),sK1)) ),
    inference(resolution,[],[f114,f137])).

fof(f137,plain,(
    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f95,f65])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) ) ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK0))
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f58,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k2_zfmisc_1(sK1,sK0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3))
      | r2_hidden(k4_tarski(sK3,X0),k2_zfmisc_1(k2_relat_1(sK2),X1)) ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK3,X0),k2_zfmisc_1(k2_relat_1(sK2),X1)) ) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:25:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.38  ipcrm: permission denied for id (789315584)
% 0.23/0.38  ipcrm: permission denied for id (791478274)
% 0.23/0.38  ipcrm: permission denied for id (791511043)
% 0.23/0.38  ipcrm: permission denied for id (791543812)
% 0.23/0.39  ipcrm: permission denied for id (791576581)
% 0.23/0.39  ipcrm: permission denied for id (789348358)
% 0.23/0.39  ipcrm: permission denied for id (789381127)
% 0.23/0.39  ipcrm: permission denied for id (791609352)
% 0.23/0.39  ipcrm: permission denied for id (791642121)
% 0.23/0.39  ipcrm: permission denied for id (791707659)
% 0.23/0.39  ipcrm: permission denied for id (789446668)
% 0.23/0.40  ipcrm: permission denied for id (791773198)
% 0.23/0.40  ipcrm: permission denied for id (791838736)
% 0.23/0.40  ipcrm: permission denied for id (789577746)
% 0.23/0.40  ipcrm: permission denied for id (789610515)
% 0.23/0.40  ipcrm: permission denied for id (791904276)
% 0.23/0.41  ipcrm: permission denied for id (791937045)
% 0.23/0.41  ipcrm: permission denied for id (792002583)
% 0.23/0.41  ipcrm: permission denied for id (792068121)
% 0.23/0.41  ipcrm: permission denied for id (792100890)
% 0.23/0.41  ipcrm: permission denied for id (792199197)
% 0.23/0.42  ipcrm: permission denied for id (792264735)
% 0.23/0.42  ipcrm: permission denied for id (792297504)
% 0.23/0.42  ipcrm: permission denied for id (789807137)
% 0.23/0.42  ipcrm: permission denied for id (789839906)
% 0.23/0.42  ipcrm: permission denied for id (789872675)
% 0.23/0.42  ipcrm: permission denied for id (792363045)
% 0.23/0.43  ipcrm: permission denied for id (792395814)
% 0.23/0.43  ipcrm: permission denied for id (792428583)
% 0.23/0.43  ipcrm: permission denied for id (792559659)
% 0.23/0.44  ipcrm: permission denied for id (792625197)
% 0.23/0.44  ipcrm: permission denied for id (792756272)
% 0.23/0.44  ipcrm: permission denied for id (792789041)
% 0.23/0.44  ipcrm: permission denied for id (792821810)
% 0.23/0.44  ipcrm: permission denied for id (792854579)
% 0.23/0.45  ipcrm: permission denied for id (790036535)
% 0.23/0.45  ipcrm: permission denied for id (792985656)
% 0.23/0.45  ipcrm: permission denied for id (790102073)
% 0.23/0.45  ipcrm: permission denied for id (793018426)
% 0.23/0.45  ipcrm: permission denied for id (790134843)
% 0.23/0.45  ipcrm: permission denied for id (793083965)
% 0.23/0.46  ipcrm: permission denied for id (793116734)
% 0.23/0.46  ipcrm: permission denied for id (793149503)
% 0.23/0.46  ipcrm: permission denied for id (793215041)
% 0.23/0.46  ipcrm: permission denied for id (793247810)
% 0.23/0.46  ipcrm: permission denied for id (793346117)
% 0.23/0.47  ipcrm: permission denied for id (793378886)
% 0.23/0.47  ipcrm: permission denied for id (793444424)
% 0.23/0.47  ipcrm: permission denied for id (793477193)
% 0.23/0.47  ipcrm: permission denied for id (790298698)
% 0.23/0.47  ipcrm: permission denied for id (790364237)
% 0.23/0.48  ipcrm: permission denied for id (793641039)
% 0.23/0.48  ipcrm: permission denied for id (793706577)
% 0.23/0.48  ipcrm: permission denied for id (790495314)
% 0.23/0.48  ipcrm: permission denied for id (790528083)
% 0.23/0.48  ipcrm: permission denied for id (790560852)
% 0.23/0.48  ipcrm: permission denied for id (790626389)
% 0.23/0.49  ipcrm: permission denied for id (793739350)
% 0.23/0.49  ipcrm: permission denied for id (793804888)
% 0.23/0.49  ipcrm: permission denied for id (790691929)
% 0.23/0.49  ipcrm: permission denied for id (790757467)
% 0.23/0.49  ipcrm: permission denied for id (793870428)
% 0.23/0.50  ipcrm: permission denied for id (790888542)
% 0.23/0.50  ipcrm: permission denied for id (790921311)
% 0.23/0.50  ipcrm: permission denied for id (793935968)
% 0.23/0.50  ipcrm: permission denied for id (790986851)
% 0.23/0.50  ipcrm: permission denied for id (791019620)
% 0.23/0.51  ipcrm: permission denied for id (791052389)
% 0.23/0.51  ipcrm: permission denied for id (791085159)
% 0.23/0.51  ipcrm: permission denied for id (794067048)
% 0.23/0.51  ipcrm: permission denied for id (791150699)
% 0.23/0.51  ipcrm: permission denied for id (794165356)
% 0.23/0.52  ipcrm: permission denied for id (791183469)
% 0.23/0.52  ipcrm: permission denied for id (794198126)
% 0.23/0.52  ipcrm: permission denied for id (791281777)
% 0.23/0.52  ipcrm: permission denied for id (794296434)
% 0.23/0.52  ipcrm: permission denied for id (794394741)
% 0.23/0.53  ipcrm: permission denied for id (791347319)
% 0.23/0.53  ipcrm: permission denied for id (794460280)
% 0.23/0.53  ipcrm: permission denied for id (794493049)
% 0.23/0.53  ipcrm: permission denied for id (794558587)
% 0.23/0.53  ipcrm: permission denied for id (794624125)
% 0.23/0.54  ipcrm: permission denied for id (794656894)
% 0.40/0.62  % (26755)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.40/0.63  % (26771)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.40/0.64  % (26768)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.40/0.65  % (26754)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.40/0.66  % (26755)Refutation found. Thanks to Tanya!
% 0.40/0.66  % SZS status Theorem for theBenchmark
% 0.40/0.66  % SZS output start Proof for theBenchmark
% 0.40/0.66  fof(f423,plain,(
% 0.40/0.66    $false),
% 0.40/0.66    inference(subsumption_resolution,[],[f416,f234])).
% 0.40/0.66  fof(f234,plain,(
% 0.40/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK7(sK2,sK3)),k2_zfmisc_1(X1,sK1))) )),
% 0.40/0.66    inference(resolution,[],[f105,f65])).
% 0.40/0.66  fof(f65,plain,(
% 0.40/0.66    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2)),
% 0.40/0.66    inference(resolution,[],[f63,f53])).
% 0.40/0.66  fof(f53,plain,(
% 0.40/0.66    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.40/0.66    inference(equality_resolution,[],[f42])).
% 0.40/0.66  fof(f42,plain,(
% 0.40/0.66    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.40/0.66    inference(cnf_transformation,[],[f31])).
% 0.40/0.66  fof(f31,plain,(
% 0.40/0.66    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.40/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).
% 0.40/0.66  fof(f28,plain,(
% 0.40/0.66    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f29,plain,(
% 0.40/0.66    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f30,plain,(
% 0.40/0.66    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f27,plain,(
% 0.40/0.66    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.40/0.66    inference(rectify,[],[f26])).
% 0.40/0.66  fof(f26,plain,(
% 0.40/0.66    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.40/0.66    inference(nnf_transformation,[],[f6])).
% 0.40/0.66  fof(f6,axiom,(
% 0.40/0.66    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.40/0.66  fof(f63,plain,(
% 0.40/0.66    r2_hidden(sK3,k2_relat_1(sK2))),
% 0.40/0.66    inference(subsumption_resolution,[],[f61,f52])).
% 0.40/0.66  fof(f52,plain,(
% 0.40/0.66    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.40/0.66    inference(equality_resolution,[],[f43])).
% 0.40/0.66  fof(f43,plain,(
% 0.40/0.66    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.40/0.66    inference(cnf_transformation,[],[f31])).
% 0.40/0.66  fof(f61,plain,(
% 0.40/0.66    r2_hidden(sK3,k2_relat_1(sK2)) | r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.40/0.66    inference(backward_demodulation,[],[f38,f56])).
% 0.40/0.66  fof(f56,plain,(
% 0.40/0.66    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.40/0.66    inference(resolution,[],[f36,f46])).
% 0.40/0.66  fof(f46,plain,(
% 0.40/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.66    inference(cnf_transformation,[],[f14])).
% 0.40/0.66  fof(f14,plain,(
% 0.40/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.66    inference(ennf_transformation,[],[f7])).
% 0.40/0.66  fof(f7,axiom,(
% 0.40/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.40/0.66  fof(f36,plain,(
% 0.40/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.40/0.66    inference(cnf_transformation,[],[f25])).
% 0.40/0.66  fof(f25,plain,(
% 0.40/0.66    ((((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & ((r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.40/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).
% 0.40/0.66  fof(f20,plain,(
% 0.40/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f21,plain,(
% 0.40/0.66    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f22,plain,(
% 0.40/0.66    ? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f23,plain,(
% 0.40/0.66    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f24,plain,(
% 0.40/0.66    ? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1))),
% 0.40/0.66    introduced(choice_axiom,[])).
% 0.40/0.66  fof(f19,plain,(
% 0.40/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.40/0.66    inference(rectify,[],[f18])).
% 0.40/0.66  fof(f18,plain,(
% 0.40/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.40/0.66    inference(nnf_transformation,[],[f10])).
% 0.40/0.66  fof(f10,plain,(
% 0.40/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.40/0.66    inference(ennf_transformation,[],[f9])).
% 0.40/0.66  fof(f9,negated_conjecture,(
% 0.40/0.66    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.40/0.66    inference(negated_conjecture,[],[f8])).
% 0.40/0.66  fof(f8,conjecture,(
% 0.40/0.66    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.40/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.40/0.66  fof(f38,plain,(
% 0.40/0.66    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.40/0.66    inference(cnf_transformation,[],[f25])).
% 0.40/0.66  fof(f105,plain,(
% 0.40/0.66    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,sK3),sK2) | ~r2_hidden(k4_tarski(X4,X3),k2_zfmisc_1(X5,sK1))) )),
% 0.40/0.66    inference(resolution,[],[f78,f50])).
% 0.40/0.66  fof(f50,plain,(
% 0.40/0.66    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.40/0.66    inference(cnf_transformation,[],[f33])).
% 0.40/0.66  fof(f33,plain,(
% 0.40/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.40/0.66    inference(flattening,[],[f32])).
% 0.40/0.66  fof(f32,plain,(
% 0.40/0.66    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.40/0.66    inference(nnf_transformation,[],[f1])).
% 0.40/0.66  % (26761)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.40/0.66  % (26759)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.40/0.67  % (26757)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.40/0.67  % (26756)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.40/0.67  fof(f1,axiom,(
% 0.40/0.67    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.40/0.67  fof(f78,plain,(
% 0.40/0.67    ( ! [X2] : (~r2_hidden(X2,sK1) | ~r2_hidden(k4_tarski(X2,sK3),sK2)) )),
% 0.40/0.67    inference(resolution,[],[f64,f40])).
% 0.40/0.67  fof(f40,plain,(
% 0.40/0.67    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f11])).
% 0.40/0.67  fof(f11,plain,(
% 0.40/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.40/0.67    inference(ennf_transformation,[],[f2])).
% 0.40/0.67  fof(f2,axiom,(
% 0.40/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.40/0.67  fof(f64,plain,(
% 0.40/0.67    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.40/0.67    inference(subsumption_resolution,[],[f62,f63])).
% 0.40/0.67  fof(f62,plain,(
% 0.40/0.67    ( ! [X4] : (~r2_hidden(sK3,k2_relat_1(sK2)) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.40/0.67    inference(backward_demodulation,[],[f39,f56])).
% 0.40/0.67  fof(f39,plain,(
% 0.40/0.67    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.40/0.67    inference(cnf_transformation,[],[f25])).
% 0.40/0.67  fof(f416,plain,(
% 0.40/0.67    r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(k2_relat_1(sK2),sK1))),
% 0.40/0.67    inference(resolution,[],[f114,f137])).
% 0.40/0.67  fof(f137,plain,(
% 0.40/0.67    r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))),
% 0.40/0.67    inference(resolution,[],[f95,f65])).
% 0.40/0.67  fof(f95,plain,(
% 0.40/0.67    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_zfmisc_1(sK1,sK0))) )),
% 0.40/0.67    inference(subsumption_resolution,[],[f94,f57])).
% 0.40/0.67  fof(f57,plain,(
% 0.40/0.67    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK1,sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.40/0.67    inference(resolution,[],[f36,f48])).
% 0.40/0.67  fof(f48,plain,(
% 0.40/0.67    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f17])).
% 0.40/0.67  fof(f17,plain,(
% 0.40/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.40/0.67    inference(ennf_transformation,[],[f5])).
% 0.40/0.67  fof(f5,axiom,(
% 0.40/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.40/0.67  fof(f94,plain,(
% 0.40/0.67    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) | v1_xboole_0(k2_zfmisc_1(sK1,sK0))) )),
% 0.40/0.67    inference(resolution,[],[f58,f41])).
% 0.40/0.67  fof(f41,plain,(
% 0.40/0.67    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f13])).
% 0.40/0.67  fof(f13,plain,(
% 0.40/0.67    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.40/0.67    inference(flattening,[],[f12])).
% 0.40/0.67  fof(f12,plain,(
% 0.40/0.67    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.40/0.67    inference(ennf_transformation,[],[f3])).
% 0.40/0.67  fof(f3,axiom,(
% 0.40/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.40/0.67  fof(f58,plain,(
% 0.40/0.67    ( ! [X1] : (m1_subset_1(X1,k2_zfmisc_1(sK1,sK0)) | ~r2_hidden(X1,sK2)) )),
% 0.40/0.67    inference(resolution,[],[f36,f47])).
% 0.40/0.67  fof(f47,plain,(
% 0.40/0.67    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f16])).
% 0.40/0.67  fof(f16,plain,(
% 0.40/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.40/0.67    inference(flattening,[],[f15])).
% 0.40/0.67  fof(f15,plain,(
% 0.40/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.40/0.67    inference(ennf_transformation,[],[f4])).
% 0.40/0.67  fof(f4,axiom,(
% 0.40/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.40/0.67  fof(f114,plain,(
% 0.40/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) | r2_hidden(k4_tarski(sK3,X0),k2_zfmisc_1(k2_relat_1(sK2),X1))) )),
% 0.40/0.67    inference(resolution,[],[f66,f49])).
% 0.40/0.67  fof(f49,plain,(
% 0.40/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.40/0.67    inference(cnf_transformation,[],[f33])).
% 0.40/0.67  fof(f66,plain,(
% 0.40/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK3,X0),k2_zfmisc_1(k2_relat_1(sK2),X1))) )),
% 0.40/0.67    inference(resolution,[],[f63,f51])).
% 0.40/0.67  fof(f51,plain,(
% 0.40/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.40/0.67    inference(cnf_transformation,[],[f33])).
% 0.40/0.67  % SZS output end Proof for theBenchmark
% 0.40/0.67  % (26755)------------------------------
% 0.40/0.67  % (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.67  % (26755)Termination reason: Refutation
% 0.40/0.67  
% 0.40/0.67  % (26755)Memory used [KB]: 2046
% 0.40/0.67  % (26755)Time elapsed: 0.082 s
% 0.40/0.67  % (26755)------------------------------
% 0.40/0.67  % (26755)------------------------------
% 0.40/0.67  % (26572)Success in time 0.298 s
%------------------------------------------------------------------------------
