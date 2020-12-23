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
% DateTime   : Thu Dec  3 12:57:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 132 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 ( 627 expanded)
%              Number of equality atoms :   49 ( 126 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f410,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f410,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3(k1_xboole_0,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f321,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f321,plain,(
    ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f308,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f308,plain,(
    r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f303,f73])).

fof(f73,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f72,f69])).

fof(f69,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f68,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f39,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f303,plain,
    ( r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f207,f41])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f207,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1,k2_relat_1(sK2)),k1_relat_1(X1))
      | k1_relat_1(X1) = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f100,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK3(X2,k2_relat_1(sK2)),sK4(X2,k2_relat_1(sK2))),X2)
      | k1_relat_1(X2) = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f80,f67])).

fof(f67,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f40,f61])).

fof(f61,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f66,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f60,f61])).

fof(f60,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (21649)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (21657)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (21657)Refutation not found, incomplete strategy% (21657)------------------------------
% 0.21/0.46  % (21657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (21657)Memory used [KB]: 6012
% 0.21/0.46  % (21657)Time elapsed: 0.002 s
% 0.21/0.46  % (21657)------------------------------
% 0.21/0.46  % (21657)------------------------------
% 0.21/0.47  % (21665)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21665)Refutation not found, incomplete strategy% (21665)------------------------------
% 0.21/0.47  % (21665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21665)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21665)Memory used [KB]: 10618
% 0.21/0.47  % (21665)Time elapsed: 0.060 s
% 0.21/0.47  % (21665)------------------------------
% 0.21/0.47  % (21665)------------------------------
% 0.21/0.48  % (21656)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (21656)Refutation not found, incomplete strategy% (21656)------------------------------
% 0.21/0.48  % (21656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21656)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21656)Memory used [KB]: 10618
% 0.21/0.48  % (21656)Time elapsed: 0.074 s
% 0.21/0.48  % (21656)------------------------------
% 0.21/0.48  % (21656)------------------------------
% 0.21/0.48  % (21649)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f410,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3(k1_xboole_0,k2_relat_1(sK2))))),
% 0.21/0.48    inference(resolution,[],[f321,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k2_relat_1(sK2)))),
% 0.21/0.48    inference(resolution,[],[f308,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f303,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(superposition,[],[f39,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f63,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f38,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.49    inference(superposition,[],[f207,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(sK3(X1,k2_relat_1(sK2)),k1_relat_1(X1)) | k1_relat_1(X1) = k2_relat_1(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f100,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(k4_tarski(sK3(X2,k2_relat_1(sK2)),sK4(X2,k2_relat_1(sK2))),X2) | k1_relat_1(X2) = k2_relat_1(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f83,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relat_1(sK2))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f40,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f38,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.21/0.49    inference(resolution,[],[f66,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f60,f61])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.49    inference(resolution,[],[f38,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21649)------------------------------
% 0.21/0.49  % (21649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21649)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21649)Memory used [KB]: 1918
% 0.21/0.49  % (21649)Time elapsed: 0.075 s
% 0.21/0.49  % (21649)------------------------------
% 0.21/0.49  % (21649)------------------------------
% 0.21/0.49  % (21644)Success in time 0.134 s
%------------------------------------------------------------------------------
