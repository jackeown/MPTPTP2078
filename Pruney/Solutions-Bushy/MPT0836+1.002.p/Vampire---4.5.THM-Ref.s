%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0836+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:44 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 244 expanded)
%              Number of leaves         :   18 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  311 (1765 expanded)
%              Number of equality atoms :   12 (  49 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(resolution,[],[f184,f70])).

fof(f70,plain,(
    r2_hidden(sK3,sK0) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK3,sK4),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X3,X5),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X3,X5),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X3,X5),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X3,X5),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & m1_subset_1(X3,sK0) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(sK3,X5),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK3,X5),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK3,sK4),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

fof(f68,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f184,plain,(
    ! [X2] : ~ r2_hidden(X2,sK0) ),
    inference(subsumption_resolution,[],[f182,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f182,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f177,f69])).

fof(f69,plain,(
    ! [X2] :
      ( r2_hidden(sK5(X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f174,f147])).

fof(f147,plain,(
    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f146,f137])).

fof(f137,plain,(
    r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f136,f58])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f136,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f130,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f130,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f43,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f145,f99])).

fof(f99,plain,(
    ! [X5] :
      ( r2_hidden(sK8(sK2,X5),sK1)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f59,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f76,f47])).

fof(f76,plain,(
    ! [X3] :
      ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f145,plain,(
    ~ r2_hidden(sK8(sK2,sK3),sK1) ),
    inference(resolution,[],[f144,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f144,plain,(
    ~ m1_subset_1(sK8(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f143,f137])).

fof(f143,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3),sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f135,f59])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3,X0),sK2)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f134,f58])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f129,f40])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f44,f53])).

fof(f44,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f174,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X15,X13))
      | ~ r2_hidden(X14,X15)
      | ~ r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
