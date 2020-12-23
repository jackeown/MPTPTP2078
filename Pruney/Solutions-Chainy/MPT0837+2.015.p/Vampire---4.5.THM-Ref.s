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
% DateTime   : Thu Dec  3 12:57:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 225 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  270 (1135 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(subsumption_resolution,[],[f121,f77])).

fof(f77,plain,(
    r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f35,f34,f33])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f75,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    inference(backward_demodulation,[],[f44,f67])).

fof(f67,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
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

fof(f27,plain,
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

fof(f28,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ! [X3] :
            ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
          <=> ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f121,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(superposition,[],[f120,f81])).

fof(f81,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f69,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f48,f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f118,f113])).

fof(f113,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK8(X1,X2,sK2),sK1)
      | ~ r2_hidden(X1,k9_relat_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f112,f69])).

fof(f112,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK8(X1,X2,sK2),sK1)
      | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f92,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f92,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f69,f66,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f66,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
      | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) ) ),
    inference(resolution,[],[f86,f78])).

fof(f78,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f76,f77])).

fof(f76,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(backward_demodulation,[],[f45,f67])).

fof(f45,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(sK8(X3,X4,sK2),X3),sK2)
      | ~ r2_hidden(X3,k9_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6822)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (6822)Refutation not found, incomplete strategy% (6822)------------------------------
% 0.20/0.47  % (6822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6830)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (6822)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6822)Memory used [KB]: 10618
% 0.20/0.47  % (6822)Time elapsed: 0.062 s
% 0.20/0.47  % (6822)------------------------------
% 0.20/0.47  % (6822)------------------------------
% 0.20/0.47  % (6838)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (6819)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (6830)Refutation not found, incomplete strategy% (6830)------------------------------
% 0.20/0.48  % (6830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6830)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (6830)Memory used [KB]: 10618
% 0.20/0.48  % (6830)Time elapsed: 0.073 s
% 0.20/0.48  % (6830)------------------------------
% 0.20/0.48  % (6830)------------------------------
% 0.20/0.48  % (6831)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (6834)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (6820)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (6834)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f121,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    r2_hidden(sK3,k2_relat_1(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f75,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f35,f34,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(rectify,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    r2_hidden(sK3,k2_relat_1(sK2)) | r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.20/0.48    inference(backward_demodulation,[],[f44,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f42,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & ((r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(rectify,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k2_relat_1(sK2))),
% 0.20/0.48    inference(superposition,[],[f120,f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f48,f42,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f118,f113])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ( ! [X2,X1] : (m1_subset_1(sK8(X1,X2,sK2),sK1) | ~r2_hidden(X1,k9_relat_1(sK2,X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f69])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X2,X1] : (m1_subset_1(sK8(X1,X2,sK2),sK1) | ~r2_hidden(X1,k9_relat_1(sK2,X2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.48    inference(resolution,[],[f95,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(rectify,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | m1_subset_1(X0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f92,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f89,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f66,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    v4_relat_1(sK2,sK1)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f42,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1)) )),
% 0.20/0.48    inference(resolution,[],[f86,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f76,f77])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(sK3,k2_relat_1(sK2)) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f45,f67])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK8(X3,X4,sK2),X3),sK2) | ~r2_hidden(X3,k9_relat_1(sK2,X4))) )),
% 0.20/0.48    inference(resolution,[],[f69,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f41])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6834)------------------------------
% 0.20/0.49  % (6834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6834)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6834)Memory used [KB]: 6140
% 0.20/0.49  % (6834)Time elapsed: 0.055 s
% 0.20/0.49  % (6834)------------------------------
% 0.20/0.49  % (6834)------------------------------
% 0.20/0.49  % (6818)Success in time 0.128 s
%------------------------------------------------------------------------------
