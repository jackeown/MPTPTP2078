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
% DateTime   : Thu Dec  3 13:07:38 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 273 expanded)
%              Number of leaves         :   16 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  377 (2382 expanded)
%              Number of equality atoms :   95 ( 563 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f288,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f288,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f39,f287])).

fof(f287,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f286,f122])).

fof(f122,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f120,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f55,f70])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f110,f66])).

fof(f66,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f28])).

% (11090)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f110,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f74,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

% (11097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(sK4)
      | k1_funct_1(k5_relat_1(sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ) ),
    inference(resolution,[],[f104,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f102,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

fof(f286,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f48,f285])).

fof(f285,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f284,f98])).

fof(f98,plain,(
    k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,X2,X3,sK3,sK4) ) ),
    inference(resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(sK3,X0) = k1_partfun1(sK1,sK2,X1,X2,sK3,X0) ) ),
    inference(resolution,[],[f92,f42])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(sK3,X0) = k1_partfun1(X3,X4,X1,X2,sK3,X0) ) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f284,plain,
    ( k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f283,f43])).

fof(f283,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK4)
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f282,f46])).

fof(f46,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f282,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK4)
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(resolution,[],[f142,f44])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(X1)
      | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(X1)
      | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f140,f42])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

fof(f48,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11096)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (11088)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (11075)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (11080)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (11082)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (11085)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (11104)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (11102)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (11078)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (11085)Refutation not found, incomplete strategy% (11085)------------------------------
% 0.20/0.53  % (11085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (11093)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.53  % (11094)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.53  % (11085)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (11085)Memory used [KB]: 10746
% 1.38/0.53  % (11085)Time elapsed: 0.130 s
% 1.38/0.53  % (11085)------------------------------
% 1.38/0.53  % (11085)------------------------------
% 1.38/0.54  % (11083)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (11102)Refutation not found, incomplete strategy% (11102)------------------------------
% 1.38/0.54  % (11102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (11083)Refutation not found, incomplete strategy% (11083)------------------------------
% 1.38/0.54  % (11083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (11083)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (11083)Memory used [KB]: 10746
% 1.38/0.54  % (11083)Time elapsed: 0.132 s
% 1.38/0.54  % (11083)------------------------------
% 1.38/0.54  % (11083)------------------------------
% 1.38/0.54  % (11095)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (11082)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % (11102)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (11102)Memory used [KB]: 6268
% 1.38/0.54  % (11102)Time elapsed: 0.130 s
% 1.38/0.54  % (11102)------------------------------
% 1.38/0.54  % (11102)------------------------------
% 1.47/0.54  % (11084)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (11098)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.55  % (11086)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (11079)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f311,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(subsumption_resolution,[],[f288,f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    v1_xboole_0(k1_xboole_0)),
% 1.47/0.55    inference(cnf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    v1_xboole_0(k1_xboole_0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.47/0.55  fof(f288,plain,(
% 1.47/0.55    ~v1_xboole_0(k1_xboole_0)),
% 1.47/0.55    inference(backward_demodulation,[],[f39,f287])).
% 1.47/0.55  fof(f287,plain,(
% 1.47/0.55    k1_xboole_0 = sK2),
% 1.47/0.55    inference(subsumption_resolution,[],[f286,f122])).
% 1.47/0.55  fof(f122,plain,(
% 1.47/0.55    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) | k1_xboole_0 = sK2),
% 1.47/0.55    inference(subsumption_resolution,[],[f120,f47])).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    k1_xboole_0 != sK1),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f27,f26,f25,f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f13,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.47/0.55    inference(flattening,[],[f12])).
% 1.47/0.55  fof(f12,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.47/0.55    inference(ennf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,negated_conjecture,(
% 1.47/0.55    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.47/0.55    inference(negated_conjecture,[],[f10])).
% 1.47/0.55  fof(f10,conjecture,(
% 1.47/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.47/0.55  fof(f120,plain,(
% 1.47/0.55    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.47/0.55    inference(resolution,[],[f117,f83])).
% 1.47/0.55  fof(f83,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.47/0.55    inference(resolution,[],[f81,f70])).
% 1.47/0.55  fof(f70,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.47/0.55    inference(resolution,[],[f57,f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f32])).
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(rectify,[],[f29])).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(nnf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.55  fof(f57,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.55    inference(rectify,[],[f35])).
% 1.47/0.55  fof(f35,plain,(
% 1.47/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.55    inference(nnf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,plain,(
% 1.47/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.55  fof(f81,plain,(
% 1.47/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.47/0.55    inference(resolution,[],[f76,f49])).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 1.47/0.55    inference(resolution,[],[f55,f70])).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(flattening,[],[f33])).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.55    inference(nnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.55  fof(f117,plain,(
% 1.47/0.55    v1_xboole_0(sK1) | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) | k1_xboole_0 = sK2),
% 1.47/0.55    inference(resolution,[],[f110,f66])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 1.47/0.55    inference(resolution,[],[f52,f45])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    m1_subset_1(sK5,sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  % (11090)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,plain,(
% 1.47/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.47/0.55    inference(flattening,[],[f14])).
% 1.47/0.55  fof(f14,plain,(
% 1.47/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.47/0.55    inference(ennf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.47/0.55  fof(f110,plain,(
% 1.47/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f108,f74])).
% 1.47/0.55  fof(f74,plain,(
% 1.47/0.55    v1_relat_1(sK4)),
% 1.47/0.55    inference(resolution,[],[f59,f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f59,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f17])).
% 1.47/0.55  fof(f17,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.55    inference(ennf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.55  % (11097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.55  fof(f108,plain,(
% 1.47/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_xboole_0 = sK2 | ~v1_relat_1(sK4) | k1_funct_1(k5_relat_1(sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1))) )),
% 1.47/0.55    inference(resolution,[],[f104,f43])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    v1_funct_1(sK4)),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f104,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f103,f40])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    v1_funct_1(sK3)),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f103,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f102,f42])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f102,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(resolution,[],[f60,f41])).
% 1.47/0.55  fof(f41,plain,(
% 1.47/0.55    v1_funct_2(sK3,sK1,sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f60,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | ~v1_funct_1(X3)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f19])).
% 1.47/0.55  fof(f19,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.47/0.55    inference(flattening,[],[f18])).
% 1.47/0.55  fof(f18,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.47/0.55    inference(ennf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).
% 1.47/0.55  fof(f286,plain,(
% 1.47/0.55    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | k1_xboole_0 = sK2),
% 1.47/0.55    inference(superposition,[],[f48,f285])).
% 1.47/0.55  fof(f285,plain,(
% 1.47/0.55    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | k1_xboole_0 = sK2),
% 1.47/0.55    inference(forward_demodulation,[],[f284,f98])).
% 1.47/0.55  fof(f98,plain,(
% 1.47/0.55    k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 1.47/0.55    inference(resolution,[],[f96,f44])).
% 1.47/0.55  fof(f96,plain,(
% 1.47/0.55    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,X2,X3,sK3,sK4)) )),
% 1.47/0.55    inference(resolution,[],[f94,f43])).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK3,X0) = k1_partfun1(sK1,sK2,X1,X2,sK3,X0)) )),
% 1.47/0.55    inference(resolution,[],[f92,f42])).
% 1.47/0.55  fof(f92,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK3,X0) = k1_partfun1(X3,X4,X1,X2,sK3,X0)) )),
% 1.47/0.55    inference(resolution,[],[f62,f40])).
% 1.47/0.55  fof(f62,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.47/0.55    inference(flattening,[],[f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.47/0.55    inference(ennf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.47/0.55  fof(f284,plain,(
% 1.47/0.55    k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f283,f43])).
% 1.47/0.55  fof(f283,plain,(
% 1.47/0.55    k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f282,f46])).
% 1.47/0.55  fof(f46,plain,(
% 1.47/0.55    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f282,plain,(
% 1.47/0.55    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 1.47/0.55    inference(resolution,[],[f142,f44])).
% 1.47/0.55  fof(f142,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | k1_xboole_0 = sK2 | ~v1_funct_1(X1) | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f141,f40])).
% 1.47/0.55  fof(f141,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f140,f42])).
% 1.47/0.55  fof(f140,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k8_funct_2(sK1,sK2,X0,sK3,X1) = k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.47/0.55    inference(resolution,[],[f61,f41])).
% 1.47/0.55  fof(f61,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | ~v1_funct_1(X3)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.47/0.55    inference(flattening,[],[f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.47/0.55    inference(ennf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).
% 1.47/0.55  fof(f48,plain,(
% 1.47/0.55    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ~v1_xboole_0(sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (11082)------------------------------
% 1.47/0.55  % (11082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (11082)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (11082)Memory used [KB]: 6524
% 1.47/0.55  % (11082)Time elapsed: 0.144 s
% 1.47/0.55  % (11082)------------------------------
% 1.47/0.55  % (11082)------------------------------
% 1.47/0.55  % (11074)Success in time 0.199 s
%------------------------------------------------------------------------------
