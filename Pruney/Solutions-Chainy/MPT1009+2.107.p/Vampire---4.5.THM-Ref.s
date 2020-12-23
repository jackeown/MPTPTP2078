%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 245 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   25
%              Number of atoms          :  461 ( 909 expanded)
%              Number of equality atoms :  233 ( 324 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f924,plain,(
    $false ),
    inference(subsumption_resolution,[],[f923,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f923,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f883,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f883,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f214,f875])).

fof(f875,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f854,f65])).

fof(f854,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f416,f842])).

fof(f842,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f837,f246])).

fof(f246,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f245,f67])).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f245,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f244,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f244,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f243,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f243,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f206,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f206,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f128,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f128,plain,(
    ! [X4,X2,X8,X5,X3,X1] : r2_hidden(X8,k4_enumset1(X8,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X6,X4,X2,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | k4_enumset1(X8,X1,X2,X3,X4,X5) != X6 ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X0 != X8
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6) != X5
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6) = X5
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X0
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6) != X5
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6) = X5
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X0
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f837,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f645,f151])).

fof(f151,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f645,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK3,k1_tarski(X1))
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ r2_hidden(sK0,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f643,f136])).

fof(f136,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f134,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(resolution,[],[f69,f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f643,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,k1_tarski(X1))
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X1))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f637,f191])).

fof(f191,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k1_tarski(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f81,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f637,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f635,f136])).

fof(f635,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f579,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f579,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f578,f151])).

fof(f578,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f568,f136])).

fof(f568,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f220,f279])).

fof(f279,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k11_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_tarski(X2)) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k11_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_tarski(X2))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f178,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f178,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f220,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f219,f136])).

fof(f219,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f215,f61])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f215,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f214,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f416,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f415,f65])).

fof(f415,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(superposition,[],[f394,f116])).

fof(f116,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f394,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,sK1),sK3)
      | sK3 = k2_zfmisc_1(X1,sK1)
      | ~ r1_tarski(k1_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f380,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f380,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK1))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f225,f62])).

fof(f225,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(k1_relat_1(X8),X9)
      | r1_tarski(X8,k2_zfmisc_1(X9,X11)) ) ),
    inference(resolution,[],[f93,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f214,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f213,f62])).

fof(f213,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f64,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21536)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (21519)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (21528)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (21517)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (21543)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (21514)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (21523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (21521)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (21539)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (21513)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (21512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (21513)Refutation not found, incomplete strategy% (21513)------------------------------
% 0.22/0.54  % (21513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21513)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21513)Memory used [KB]: 1791
% 0.22/0.54  % (21513)Time elapsed: 0.118 s
% 0.22/0.54  % (21513)------------------------------
% 0.22/0.54  % (21513)------------------------------
% 0.22/0.54  % (21515)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (21540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (21516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (21532)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (21541)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (21533)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (21518)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (21541)Refutation not found, incomplete strategy% (21541)------------------------------
% 0.22/0.55  % (21541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21537)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (21541)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21541)Memory used [KB]: 6268
% 0.22/0.55  % (21541)Time elapsed: 0.132 s
% 0.22/0.55  % (21541)------------------------------
% 0.22/0.55  % (21541)------------------------------
% 0.22/0.55  % (21534)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (21538)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (21525)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (21524)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (21531)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (21529)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (21523)Refutation not found, incomplete strategy% (21523)------------------------------
% 0.22/0.55  % (21523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21523)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21523)Memory used [KB]: 10874
% 0.22/0.55  % (21523)Time elapsed: 0.137 s
% 0.22/0.55  % (21523)------------------------------
% 0.22/0.55  % (21523)------------------------------
% 0.22/0.55  % (21526)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (21542)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (21539)Refutation not found, incomplete strategy% (21539)------------------------------
% 0.22/0.55  % (21539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21520)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (21535)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (21531)Refutation not found, incomplete strategy% (21531)------------------------------
% 0.22/0.56  % (21531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21539)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21539)Memory used [KB]: 10746
% 0.22/0.56  % (21539)Time elapsed: 0.143 s
% 0.22/0.56  % (21539)------------------------------
% 0.22/0.56  % (21539)------------------------------
% 0.22/0.57  % (21531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (21531)Memory used [KB]: 10746
% 0.22/0.57  % (21531)Time elapsed: 0.142 s
% 0.22/0.57  % (21531)------------------------------
% 0.22/0.57  % (21531)------------------------------
% 0.22/0.57  % (21544)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (21544)Refutation not found, incomplete strategy% (21544)------------------------------
% 0.22/0.57  % (21544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (21544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (21544)Memory used [KB]: 1791
% 0.22/0.57  % (21544)Time elapsed: 0.145 s
% 0.22/0.57  % (21544)------------------------------
% 0.22/0.57  % (21544)------------------------------
% 0.22/0.58  % (21533)Refutation not found, incomplete strategy% (21533)------------------------------
% 0.22/0.58  % (21533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (21533)Memory used [KB]: 1918
% 0.22/0.58  % (21533)Time elapsed: 0.160 s
% 0.22/0.58  % (21533)------------------------------
% 0.22/0.58  % (21533)------------------------------
% 0.22/0.58  % (21542)Refutation not found, incomplete strategy% (21542)------------------------------
% 0.22/0.58  % (21542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21542)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (21542)Memory used [KB]: 6268
% 0.22/0.58  % (21542)Time elapsed: 0.160 s
% 0.22/0.58  % (21542)------------------------------
% 0.22/0.58  % (21542)------------------------------
% 0.22/0.59  % (21521)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f924,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f923,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.81/0.61  fof(f923,plain,(
% 1.81/0.61    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.81/0.61    inference(forward_demodulation,[],[f883,f66])).
% 1.81/0.61  fof(f66,plain,(
% 1.81/0.61    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f20])).
% 1.81/0.61  fof(f20,axiom,(
% 1.81/0.61    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.81/0.61  fof(f883,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.81/0.61    inference(backward_demodulation,[],[f214,f875])).
% 1.81/0.61  fof(f875,plain,(
% 1.81/0.61    k1_xboole_0 = sK3),
% 1.81/0.61    inference(subsumption_resolution,[],[f854,f65])).
% 1.81/0.61  fof(f854,plain,(
% 1.81/0.61    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK3),
% 1.81/0.61    inference(backward_demodulation,[],[f416,f842])).
% 1.81/0.61  fof(f842,plain,(
% 1.81/0.61    k1_xboole_0 = k1_relat_1(sK3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f837,f246])).
% 1.81/0.61  fof(f246,plain,(
% 1.81/0.61    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.81/0.61    inference(superposition,[],[f245,f67])).
% 1.81/0.61  fof(f67,plain,(
% 1.81/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.81/0.61  fof(f245,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.81/0.61    inference(superposition,[],[f244,f71])).
% 1.81/0.61  fof(f71,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.61  fof(f244,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.81/0.61    inference(superposition,[],[f243,f89])).
% 1.81/0.61  fof(f89,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.61  fof(f243,plain,(
% 1.81/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X0,X1,X2,X3))) )),
% 1.81/0.61    inference(superposition,[],[f206,f91])).
% 1.81/0.61  fof(f91,plain,(
% 1.81/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.81/0.61  fof(f206,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.81/0.61    inference(superposition,[],[f128,f94])).
% 1.81/0.61  fof(f94,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.81/0.61  fof(f128,plain,(
% 1.81/0.61    ( ! [X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,k4_enumset1(X8,X1,X2,X3,X4,X5))) )),
% 1.81/0.61    inference(equality_resolution,[],[f127])).
% 1.81/0.61  fof(f127,plain,(
% 1.81/0.61    ( ! [X6,X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,X6) | k4_enumset1(X8,X1,X2,X3,X4,X5) != X6) )),
% 1.81/0.61    inference(equality_resolution,[],[f98])).
% 1.81/0.61  fof(f98,plain,(
% 1.81/0.61    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X0 != X8 | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.81/0.61    inference(cnf_transformation,[],[f60])).
% 1.81/0.61  fof(f60,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | (((sK4(X0,X1,X2,X3,X4,X5,X6) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK4(X0,X1,X2,X3,X4,X5,X6) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).
% 1.81/0.61  fof(f59,plain,(
% 1.81/0.61    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6))) => (((sK4(X0,X1,X2,X3,X4,X5,X6) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK4(X0,X1,X2,X3,X4,X5,X6) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f58,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.81/0.61    inference(rectify,[],[f57])).
% 1.81/0.61  fof(f57,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.81/0.61    inference(flattening,[],[f56])).
% 1.81/0.61  fof(f56,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.81/0.61    inference(nnf_transformation,[],[f45])).
% 1.81/0.61  fof(f45,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.81/0.61    inference(ennf_transformation,[],[f12])).
% 1.81/0.61  fof(f12,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 1.81/0.61  fof(f837,plain,(
% 1.81/0.61    k1_xboole_0 = k1_relat_1(sK3) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.81/0.61    inference(resolution,[],[f645,f151])).
% 1.81/0.61  fof(f151,plain,(
% 1.81/0.61    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.81/0.61    inference(resolution,[],[f90,f62])).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f47])).
% 1.81/0.61  fof(f47,plain,(
% 1.81/0.61    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f46])).
% 1.81/0.61  fof(f46,plain,(
% 1.81/0.61    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.81/0.61    inference(flattening,[],[f30])).
% 1.81/0.61  fof(f30,plain,(
% 1.81/0.61    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.81/0.61    inference(ennf_transformation,[],[f28])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.81/0.61    inference(pure_predicate_removal,[],[f27])).
% 1.81/0.61  fof(f27,negated_conjecture,(
% 1.81/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.81/0.61    inference(negated_conjecture,[],[f26])).
% 1.81/0.61  fof(f26,conjecture,(
% 1.81/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.81/0.61  fof(f90,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f41])).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.61    inference(ennf_transformation,[],[f29])).
% 1.81/0.61  fof(f29,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.81/0.61    inference(pure_predicate_removal,[],[f23])).
% 1.81/0.61  fof(f23,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.81/0.61  fof(f645,plain,(
% 1.81/0.61    ( ! [X1] : (~v4_relat_1(sK3,k1_tarski(X1)) | k1_xboole_0 = k1_relat_1(sK3) | ~r2_hidden(sK0,k1_tarski(X1))) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f643,f136])).
% 1.81/0.61  fof(f136,plain,(
% 1.81/0.61    v1_relat_1(sK3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f134,f70])).
% 1.81/0.61  fof(f70,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f17])).
% 1.81/0.61  fof(f17,axiom,(
% 1.81/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.81/0.61  fof(f134,plain,(
% 1.81/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))),
% 1.81/0.61    inference(resolution,[],[f69,f62])).
% 1.81/0.61  fof(f69,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f33])).
% 1.81/0.61  fof(f33,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f14])).
% 1.81/0.61  fof(f14,axiom,(
% 1.81/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.81/0.61  fof(f643,plain,(
% 1.81/0.61    ( ! [X1] : (~r2_hidden(sK0,k1_tarski(X1)) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X1)) | ~v1_relat_1(sK3)) )),
% 1.81/0.61    inference(superposition,[],[f637,f191])).
% 1.81/0.61  fof(f191,plain,(
% 1.81/0.61    ( ! [X2,X3] : (k1_relat_1(X2) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k1_tarski(X3)) | ~v1_relat_1(X2)) )),
% 1.81/0.61    inference(resolution,[],[f81,f74])).
% 1.81/0.61  fof(f74,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f48])).
% 1.81/0.61  fof(f48,plain,(
% 1.81/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(nnf_transformation,[],[f36])).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f16])).
% 1.81/0.61  fof(f16,axiom,(
% 1.81/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.81/0.61  fof(f81,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f52])).
% 1.81/0.61  fof(f52,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.81/0.61    inference(flattening,[],[f51])).
% 1.81/0.61  fof(f51,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.81/0.61    inference(nnf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.81/0.61  fof(f637,plain,(
% 1.81/0.61    ~r2_hidden(sK0,k1_relat_1(sK3))),
% 1.81/0.61    inference(subsumption_resolution,[],[f635,f136])).
% 1.81/0.61  fof(f635,plain,(
% 1.81/0.61    ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.81/0.61    inference(resolution,[],[f579,f72])).
% 1.81/0.61  fof(f72,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f34])).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f18])).
% 1.81/0.61  fof(f18,axiom,(
% 1.81/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.81/0.61  fof(f579,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~r2_hidden(sK0,k1_relat_1(sK3))),
% 1.81/0.61    inference(subsumption_resolution,[],[f578,f151])).
% 1.81/0.61  fof(f578,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v4_relat_1(sK3,k1_tarski(sK0))),
% 1.81/0.61    inference(subsumption_resolution,[],[f568,f136])).
% 1.81/0.61  fof(f568,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(sK0))),
% 1.81/0.61    inference(superposition,[],[f220,f279])).
% 1.81/0.61  fof(f279,plain,(
% 1.81/0.61    ( ! [X2,X1] : (k2_relat_1(X1) = k11_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v4_relat_1(X1,k1_tarski(X2))) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f269])).
% 1.81/0.61  fof(f269,plain,(
% 1.81/0.61    ( ! [X2,X1] : (k2_relat_1(X1) = k11_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v4_relat_1(X1,k1_tarski(X2)) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(superposition,[],[f178,f68])).
% 1.81/0.61  fof(f68,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f32])).
% 1.81/0.61  fof(f32,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f15])).
% 1.81/0.61  fof(f15,axiom,(
% 1.81/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.81/0.61  fof(f178,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f177])).
% 1.81/0.61  fof(f177,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(superposition,[],[f73,f77])).
% 1.81/0.61  fof(f77,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f40])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(flattening,[],[f39])).
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,axiom,(
% 1.81/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.81/0.61  fof(f73,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f35])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f19])).
% 1.81/0.61  fof(f19,axiom,(
% 1.81/0.61    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.81/0.61  fof(f220,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK3))),
% 1.81/0.61    inference(subsumption_resolution,[],[f219,f136])).
% 1.81/0.61  fof(f219,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.81/0.61    inference(subsumption_resolution,[],[f215,f61])).
% 1.81/0.61  fof(f61,plain,(
% 1.81/0.61    v1_funct_1(sK3)),
% 1.81/0.61    inference(cnf_transformation,[],[f47])).
% 1.81/0.61  fof(f215,plain,(
% 1.81/0.61    ~r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.81/0.61    inference(superposition,[],[f214,f76])).
% 1.81/0.61  fof(f76,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(flattening,[],[f37])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f22])).
% 1.81/0.61  fof(f22,axiom,(
% 1.81/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.81/0.61  fof(f416,plain,(
% 1.81/0.61    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | k1_xboole_0 = sK3),
% 1.81/0.61    inference(subsumption_resolution,[],[f415,f65])).
% 1.81/0.61  fof(f415,plain,(
% 1.81/0.61    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 1.81/0.61    inference(superposition,[],[f394,f116])).
% 1.81/0.61  fof(f116,plain,(
% 1.81/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.81/0.61    inference(equality_resolution,[],[f87])).
% 1.81/0.61  fof(f87,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f55])).
% 1.81/0.61  fof(f55,plain,(
% 1.81/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.81/0.61    inference(flattening,[],[f54])).
% 1.81/0.61  fof(f54,plain,(
% 1.81/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.81/0.61    inference(nnf_transformation,[],[f11])).
% 1.81/0.61  fof(f11,axiom,(
% 1.81/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.81/0.61  fof(f394,plain,(
% 1.81/0.61    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(X1,sK1),sK3) | sK3 = k2_zfmisc_1(X1,sK1) | ~r1_tarski(k1_relat_1(sK3),X1)) )),
% 1.81/0.61    inference(resolution,[],[f380,f80])).
% 1.81/0.61  fof(f80,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(flattening,[],[f49])).
% 1.81/0.61  fof(f49,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(nnf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.61  fof(f380,plain,(
% 1.81/0.61    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 1.81/0.61    inference(resolution,[],[f225,f62])).
% 1.81/0.61  fof(f225,plain,(
% 1.81/0.61    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~r1_tarski(k1_relat_1(X8),X9) | r1_tarski(X8,k2_zfmisc_1(X9,X11))) )),
% 1.81/0.61    inference(resolution,[],[f93,f84])).
% 1.81/0.61  fof(f84,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f53])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.81/0.61    inference(nnf_transformation,[],[f13])).
% 1.81/0.61  fof(f13,axiom,(
% 1.81/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.81/0.62  fof(f93,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f44])).
% 1.81/0.62  fof(f44,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.81/0.62    inference(flattening,[],[f43])).
% 1.81/0.62  fof(f43,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.81/0.62    inference(ennf_transformation,[],[f25])).
% 1.81/0.62  fof(f25,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 1.81/0.62  fof(f214,plain,(
% 1.81/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.81/0.62    inference(subsumption_resolution,[],[f213,f62])).
% 1.81/0.62  fof(f213,plain,(
% 1.81/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.81/0.62    inference(superposition,[],[f64,f92])).
% 1.81/0.62  fof(f92,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f42])).
% 1.81/0.62  fof(f42,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(ennf_transformation,[],[f24])).
% 1.81/0.62  fof(f24,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.81/0.62  fof(f64,plain,(
% 1.81/0.62    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (21521)------------------------------
% 1.81/0.62  % (21521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (21521)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (21521)Memory used [KB]: 2174
% 1.81/0.62  % (21521)Time elapsed: 0.168 s
% 1.81/0.62  % (21521)------------------------------
% 1.81/0.62  % (21521)------------------------------
% 1.81/0.62  % (21506)Success in time 0.245 s
%------------------------------------------------------------------------------
