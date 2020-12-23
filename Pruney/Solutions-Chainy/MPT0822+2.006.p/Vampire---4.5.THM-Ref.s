%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 583 expanded)
%              Number of leaves         :   13 ( 208 expanded)
%              Depth                    :   22
%              Number of atoms          :  220 (2897 expanded)
%              Number of equality atoms :   51 ( 640 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f124])).

fof(f124,plain,(
    r2_hidden(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f49,f113])).

fof(f113,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f110,f101])).

fof(f101,plain,
    ( sK1 = k2_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f23,f26,f25,f24])).

% (5569)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f24,plain,(
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

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f85,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,
    ( sK1 = k2_relat_1(sK2)
    | r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2)
    | ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2)
    | r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2)
    | sK1 = k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK4(sK5(X4,sK1)),sK5(X4,sK1)),sK2)
      | sK1 = k2_relat_1(sK2)
      | sK1 = k2_relat_1(X4)
      | r2_hidden(k4_tarski(sK6(X4,sK1),sK5(X4,sK1)),X4) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | sK1 = k2_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f29,f46])).

fof(f46,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
     => r2_hidden(k4_tarski(sK4(X5),X5),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f29,plain,(
    ! [X5] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f61,f51])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f47,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f45,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2)
    | ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(resolution,[],[f86,f38])).

fof(f49,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f30,f46])).

fof(f30,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(forward_demodulation,[],[f125,f113])).

fof(f125,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,(
    ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2) ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,(
    ! [X4] :
      ( sK1 != sK1
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(backward_demodulation,[],[f50,f113])).

fof(f50,plain,(
    ! [X4] :
      ( sK1 != k2_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(backward_demodulation,[],[f31,f46])).

fof(f31,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f21])).

% (5561)Refutation not found, incomplete strategy% (5561)------------------------------
% (5561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5561)Termination reason: Refutation not found, incomplete strategy

% (5561)Memory used [KB]: 10618
% (5561)Time elapsed: 0.071 s
% (5561)------------------------------
% (5561)------------------------------
% (5566)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (5563)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (5570)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5561)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (5558)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (5574)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (5565)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (5562)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (5571)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (5562)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    r2_hidden(sK3,sK1)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    sK1 != sK1 | r2_hidden(sK3,sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f49,f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f110,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f86,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f23,f26,f25,f24])).
% 0.22/0.48  % (5569)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2) | sK1 = k2_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f85,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2) | ~r2_hidden(sK5(sK2,sK1),sK1)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | sK1 = k2_relat_1(sK2) | r2_hidden(k4_tarski(sK6(sK2,sK1),sK5(sK2,sK1)),sK2) | sK1 = k2_relat_1(sK2) | ~r2_hidden(sK5(sK2,sK1),sK1)),
% 0.22/0.48    inference(resolution,[],[f60,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X4] : (r2_hidden(k4_tarski(sK4(sK5(X4,sK1)),sK5(X4,sK1)),sK2) | sK1 = k2_relat_1(sK2) | sK1 = k2_relat_1(X4) | r2_hidden(k4_tarski(sK6(X4,sK1),sK5(X4,sK1)),X4)) )),
% 0.22/0.48    inference(resolution,[],[f48,f37])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(k4_tarski(sK4(X5),X5),sK2) | sK1 = k2_relat_1(sK2)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f29,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.48    inference(resolution,[],[f28,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    (sK1 != k2_relset_1(sK0,sK1,sK2) | (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) => r2_hidden(k4_tarski(sK4(X5),X5),sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(rectify,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X5] : (sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | ~r2_hidden(sK5(sK2,sK1),k2_relat_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f102,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f61,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f28,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.48    inference(resolution,[],[f45,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v5_relat_1(sK2,sK1)),
% 0.22/0.48    inference(resolution,[],[f28,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ~r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | sK1 = k2_relat_1(sK2) | ~r2_hidden(sK5(sK2,sK1),sK1)),
% 0.22/0.48    inference(resolution,[],[f86,f38])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    r2_hidden(sK3,sK1) | sK1 != k2_relat_1(sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f30,f46])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~r2_hidden(sK3,sK1)),
% 0.22/0.48    inference(forward_demodulation,[],[f125,f113])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~r2_hidden(sK3,k2_relat_1(sK2))),
% 0.22/0.48    inference(resolution,[],[f123,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.48    inference(equality_resolution,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X4] : (sK1 != sK1 | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f50,f113])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X4] : (sK1 != k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f31,f46])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  % (5561)Refutation not found, incomplete strategy% (5561)------------------------------
% 0.22/0.48  % (5561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5561)Memory used [KB]: 10618
% 0.22/0.48  % (5561)Time elapsed: 0.071 s
% 0.22/0.48  % (5561)------------------------------
% 0.22/0.48  % (5561)------------------------------
% 0.22/0.48  % (5566)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (5563)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (5570)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (5562)------------------------------
% 0.22/0.48  % (5562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5562)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (5562)Memory used [KB]: 1791
% 0.22/0.48  % (5562)Time elapsed: 0.063 s
% 0.22/0.48  % (5562)------------------------------
% 0.22/0.48  % (5562)------------------------------
% 0.22/0.48  % (5555)Success in time 0.117 s
%------------------------------------------------------------------------------
