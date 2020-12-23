%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 326 expanded)
%              Number of leaves         :   15 ( 116 expanded)
%              Depth                    :   22
%              Number of atoms          :  296 (1722 expanded)
%              Number of equality atoms :   86 ( 183 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(subsumption_resolution,[],[f649,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f649,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f72,f644])).

fof(f644,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f637,f56])).

fof(f637,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f633])).

fof(f633,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f626,f56])).

fof(f626,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f76,f622])).

fof(f622,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f621,f59])).

fof(f59,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f57,plain,(
    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                  & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5)
                | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
              & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5)
              | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
            & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),sK6)
            | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5)
            | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
          & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,sK6))
          & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),sK6)
          | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5)
          | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
        & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,sK6))
        & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
        | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
        | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
      & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
      & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f621,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f620])).

fof(f620,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f619,f265])).

fof(f265,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f263,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f263,plain,
    ( sP0(sK7,sK3,sK2,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f34,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP0(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP0(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f16,f18])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f619,plain,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f618,f64])).

fof(f64,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(resolution,[],[f44,f57])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f618,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f617])).

fof(f617,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f268,f264])).

fof(f264,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f263,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f268,plain,
    ( ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f267,f62])).

fof(f62,plain,(
    r2_hidden(k2_mcart_1(sK7),sK6) ),
    inference(resolution,[],[f44,f50])).

fof(f267,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f36,f266])).

fof(f266,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f263,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f69,f62])).

fof(f69,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK6)
      | ~ v1_xboole_0(sK3) ) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f74,f66])).

fof(f66,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
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

fof(f74,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK5)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f71,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f59,f39])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f67,f40])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (21935)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (21928)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (21935)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f656,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f649,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(resolution,[],[f55,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(resolution,[],[f41,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.45  fof(f649,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(backward_demodulation,[],[f72,f644])).
% 0.21/0.45  fof(f644,plain,(
% 0.21/0.45    k1_xboole_0 = sK1),
% 0.21/0.45    inference(subsumption_resolution,[],[f637,f56])).
% 0.21/0.45  fof(f637,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.45    inference(superposition,[],[f75,f633])).
% 0.21/0.45  fof(f633,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.45    inference(subsumption_resolution,[],[f626,f56])).
% 0.21/0.45  fof(f626,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.45    inference(superposition,[],[f76,f622])).
% 0.21/0.45  fof(f622,plain,(
% 0.21/0.45    k1_xboole_0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.45    inference(subsumption_resolution,[],[f621,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)),
% 0.21/0.45    inference(resolution,[],[f57,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))),
% 0.21/0.45    inference(resolution,[],[f43,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.45    inference(definition_unfolding,[],[f35,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f23,f22,f21,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) => ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.21/0.45  fof(f621,plain,(
% 0.21/0.45    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f620])).
% 0.21/0.45  fof(f620,plain,(
% 0.21/0.45    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(superposition,[],[f619,f265])).
% 0.21/0.45  fof(f265,plain,(
% 0.21/0.45    k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(resolution,[],[f263,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP0(X0,X1,X2,X3))),
% 0.21/0.45    inference(rectify,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP0(X3,X2,X1,X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP0(X3,X2,X1,X0))),
% 0.21/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.45  fof(f263,plain,(
% 0.21/0.45    sP0(sK7,sK3,sK2,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.45    inference(resolution,[],[f52,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f42])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP0(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f48,f42])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (! [X3] : (sP0(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.45    inference(definition_folding,[],[f16,f18])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.45  fof(f619,plain,(
% 0.21/0.45    ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(subsumption_resolution,[],[f618,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)),
% 0.21/0.45    inference(resolution,[],[f44,f57])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f618,plain,(
% 0.21/0.45    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f617])).
% 0.21/0.45  fof(f617,plain,(
% 0.21/0.45    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(superposition,[],[f268,f264])).
% 0.21/0.45  fof(f264,plain,(
% 0.21/0.45    k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(resolution,[],[f263,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f268,plain,(
% 0.21/0.45    ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.45    inference(subsumption_resolution,[],[f267,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    r2_hidden(k2_mcart_1(sK7),sK6)),
% 0.21/0.46    inference(resolution,[],[f44,f50])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    ~r2_hidden(k2_mcart_1(sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.46    inference(superposition,[],[f36,f266])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.21/0.46    inference(resolution,[],[f263,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ~v1_xboole_0(sK3)),
% 0.21/0.46    inference(resolution,[],[f69,f62])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X2] : (~r2_hidden(X2,sK6) | ~v1_xboole_0(sK3)) )),
% 0.21/0.46    inference(resolution,[],[f49,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ~v1_xboole_0(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f74,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~v1_xboole_0(sK5)),
% 0.21/0.46    inference(resolution,[],[f64,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.46    inference(rectify,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ~v1_xboole_0(sK2) | v1_xboole_0(sK5)),
% 0.21/0.46    inference(resolution,[],[f68,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK5) | ~v1_xboole_0(sK2)) )),
% 0.21/0.46    inference(resolution,[],[f49,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f71,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ~v1_xboole_0(sK4)),
% 0.21/0.46    inference(resolution,[],[f59,f39])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1) | v1_xboole_0(sK4)),
% 0.21/0.46    inference(resolution,[],[f67,f40])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v1_xboole_0(sK1)) )),
% 0.21/0.46    inference(resolution,[],[f49,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21935)------------------------------
% 0.21/0.46  % (21935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21935)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21935)Memory used [KB]: 2302
% 0.21/0.46  % (21935)Time elapsed: 0.045 s
% 0.21/0.46  % (21935)------------------------------
% 0.21/0.46  % (21935)------------------------------
% 0.21/0.46  % (21919)Success in time 0.098 s
%------------------------------------------------------------------------------
