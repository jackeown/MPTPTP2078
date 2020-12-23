%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:31 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  121 (1867 expanded)
%              Number of leaves         :   19 ( 631 expanded)
%              Depth                    :   29
%              Number of atoms          :  449 (16553 expanded)
%              Number of equality atoms :   67 (5145 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f486,plain,(
    $false ),
    inference(resolution,[],[f481,f394])).

fof(f394,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f387,f202])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f137,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f137,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f136,f113])).

fof(f113,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f102,f101])).

fof(f101,plain,(
    sK2 = sK6(sK0,sK1,sK2) ),
    inference(resolution,[],[f50,f96])).

fof(f96,plain,(
    ! [X6,X0,X1] :
      ( sK6(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X2,X0,X1] :
      ( sK6(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK4(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X1)
              & k1_relat_1(sK5(X0,X1,X2)) = X0
              & sK4(X0,X1,X2) = sK5(X0,X1,X2)
              & v1_funct_1(sK5(X0,X1,X2))
              & v1_relat_1(sK5(X0,X1,X2)) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1)
                & k1_relat_1(sK6(X0,X1,X6)) = X0
                & sK6(X0,X1,X6) = X6
                & v1_funct_1(sK6(X0,X1,X6))
                & v1_relat_1(sK6(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK4(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK4(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK4(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X1)
        & k1_relat_1(sK5(X0,X1,X2)) = X0
        & sK4(X0,X1,X2) = sK5(X0,X1,X2)
        & v1_funct_1(sK5(X0,X1,X2))
        & v1_relat_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1)
        & k1_relat_1(sK6(X0,X1,X6)) = X0
        & sK6(X0,X1,X6) = X6
        & v1_funct_1(sK6(X0,X1,X6))
        & v1_relat_1(sK6(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f50,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f102,plain,(
    sK0 = k1_relat_1(sK6(sK0,sK1,sK2)) ),
    inference(resolution,[],[f50,f95])).

fof(f95,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK6(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK6(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f136,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f127,f112])).

fof(f112,plain,(
    v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f99,f101])).

fof(f99,plain,(
    v1_relat_1(sK6(sK0,sK1,sK2)) ),
    inference(resolution,[],[f50,f98])).

fof(f98,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f111,plain,(
    v1_funct_1(sK2) ),
    inference(backward_demodulation,[],[f100,f101])).

fof(f100,plain,(
    v1_funct_1(sK6(sK0,sK1,sK2)) ),
    inference(resolution,[],[f50,f97])).

fof(f97,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f387,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f385,f187])).

fof(f187,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f186,f137])).

fof(f186,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f185,f111])).

fof(f185,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f135,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f135,plain,(
    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f134,f113])).

fof(f134,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f126,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f385,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f382,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f382,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f184,f182])).

fof(f182,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ r1_tarski(sK0,X1) ) ),
    inference(forward_demodulation,[],[f181,f113])).

fof(f181,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(subsumption_resolution,[],[f166,f112])).

fof(f166,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f114,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f114,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f103,f101])).

fof(f103,plain,(
    r1_tarski(k2_relat_1(sK6(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f50,f94])).

fof(f94,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f183,f111])).

fof(f183,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f121,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f120,f89])).

fof(f120,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f119,f113])).

fof(f119,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f118,f112])).

fof(f118,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f114])).

fof(f117,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f111])).

fof(f115,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f69])).

fof(f51,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f481,plain,(
    ! [X7] : ~ v1_xboole_0(X7) ),
    inference(subsumption_resolution,[],[f477,f386])).

fof(f386,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f385,f201])).

fof(f201,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f477,plain,(
    ! [X7] :
      ( v1_xboole_0(sK0)
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f457,f59])).

fof(f457,plain,(
    ! [X4] : m1_subset_1(sK0,k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f451,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f451,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(resolution,[],[f443,f151])).

fof(f151,plain,(
    ! [X5] :
      ( ~ v4_relat_1(sK2,X5)
      | r1_tarski(sK0,X5) ) ),
    inference(forward_demodulation,[],[f141,f113])).

fof(f141,plain,(
    ! [X5] :
      ( r1_tarski(k1_relat_1(sK2),X5)
      | ~ v4_relat_1(sK2,X5) ) ),
    inference(resolution,[],[f112,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f443,plain,(
    ! [X5] : v4_relat_1(sK2,X5) ),
    inference(resolution,[],[f432,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f432,plain,(
    ! [X4] : m1_subset_1(sK2,k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f422,f68])).

fof(f422,plain,(
    ! [X2] : r1_tarski(sK2,X2) ),
    inference(resolution,[],[f411,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f411,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(resolution,[],[f409,f89])).

fof(f409,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f406,f68])).

fof(f406,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f394,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:45:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (20119)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.47  % (20127)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.48  % (20127)Refutation not found, incomplete strategy% (20127)------------------------------
% 0.20/0.48  % (20127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20126)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (20134)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (20120)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (20127)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20127)Memory used [KB]: 10874
% 0.20/0.49  % (20127)Time elapsed: 0.092 s
% 0.20/0.49  % (20127)------------------------------
% 0.20/0.49  % (20127)------------------------------
% 0.20/0.49  % (20121)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (20144)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (20124)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (20122)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (20143)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (20142)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (20136)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (20123)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (20148)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (20141)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (20135)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (20140)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (20129)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (20131)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (20133)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (20132)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (20130)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (20138)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (20129)Refutation not found, incomplete strategy% (20129)------------------------------
% 0.20/0.52  % (20129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20129)Memory used [KB]: 10746
% 0.20/0.52  % (20129)Time elapsed: 0.108 s
% 0.20/0.52  % (20129)------------------------------
% 0.20/0.52  % (20129)------------------------------
% 0.20/0.52  % (20147)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (20145)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.53  % (20142)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f486,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(resolution,[],[f481,f394])).
% 1.36/0.53  fof(f394,plain,(
% 1.36/0.53    v1_xboole_0(sK2)),
% 1.36/0.53    inference(resolution,[],[f387,f202])).
% 1.36/0.53  fof(f202,plain,(
% 1.36/0.53    ~v1_xboole_0(k2_relat_1(sK2)) | v1_xboole_0(sK2)),
% 1.36/0.53    inference(resolution,[],[f137,f59])).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.36/0.53  fof(f137,plain,(
% 1.36/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 1.36/0.53    inference(forward_demodulation,[],[f136,f113])).
% 1.36/0.53  fof(f113,plain,(
% 1.36/0.53    sK0 = k1_relat_1(sK2)),
% 1.36/0.53    inference(forward_demodulation,[],[f102,f101])).
% 1.36/0.53  fof(f101,plain,(
% 1.36/0.53    sK2 = sK6(sK0,sK1,sK2)),
% 1.36/0.53    inference(resolution,[],[f50,f96])).
% 1.36/0.53  fof(f96,plain,(
% 1.36/0.53    ( ! [X6,X0,X1] : (sK6(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.36/0.53    inference(equality_resolution,[],[f77])).
% 1.36/0.53  fof(f77,plain,(
% 1.36/0.53    ( ! [X6,X2,X0,X1] : (sK6(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X1) & k1_relat_1(sK5(X0,X1,X2)) = X0 & sK4(X0,X1,X2) = sK5(X0,X1,X2) & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1) & k1_relat_1(sK6(X0,X1,X6)) = X0 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f45,f48,f47,f46])).
% 1.36/0.53  fof(f46,plain,(
% 1.36/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK4(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f47,plain,(
% 1.36/0.53    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK4(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X1) & k1_relat_1(sK5(X0,X1,X2)) = X0 & sK4(X0,X1,X2) = sK5(X0,X1,X2) & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1) & k1_relat_1(sK6(X0,X1,X6)) = X0 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f45,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.36/0.53    inference(rectify,[],[f44])).
% 1.36/0.53  fof(f44,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.36/0.53    inference(nnf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 1.36/0.53  fof(f50,plain,(
% 1.36/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.36/0.53    inference(negated_conjecture,[],[f15])).
% 1.36/0.53  fof(f15,conjecture,(
% 1.36/0.53    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 1.36/0.53  fof(f102,plain,(
% 1.36/0.53    sK0 = k1_relat_1(sK6(sK0,sK1,sK2))),
% 1.36/0.53    inference(resolution,[],[f50,f95])).
% 1.36/0.53  fof(f95,plain,(
% 1.36/0.53    ( ! [X6,X0,X1] : (k1_relat_1(sK6(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.36/0.53    inference(equality_resolution,[],[f78])).
% 1.36/0.53  fof(f78,plain,(
% 1.36/0.53    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK6(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f136,plain,(
% 1.36/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.36/0.53    inference(subsumption_resolution,[],[f127,f112])).
% 1.36/0.53  fof(f112,plain,(
% 1.36/0.53    v1_relat_1(sK2)),
% 1.36/0.53    inference(backward_demodulation,[],[f99,f101])).
% 1.36/0.53  fof(f99,plain,(
% 1.36/0.53    v1_relat_1(sK6(sK0,sK1,sK2))),
% 1.36/0.53    inference(resolution,[],[f50,f98])).
% 1.36/0.53  fof(f98,plain,(
% 1.36/0.53    ( ! [X6,X0,X1] : (v1_relat_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.36/0.53    inference(equality_resolution,[],[f75])).
% 1.36/0.53  fof(f75,plain,(
% 1.36/0.53    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f127,plain,(
% 1.36/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 1.36/0.53    inference(resolution,[],[f111,f54])).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f19])).
% 1.36/0.53  fof(f19,plain,(
% 1.36/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(flattening,[],[f18])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f14])).
% 1.36/0.53  fof(f14,axiom,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.36/0.53  fof(f111,plain,(
% 1.36/0.53    v1_funct_1(sK2)),
% 1.36/0.53    inference(backward_demodulation,[],[f100,f101])).
% 1.36/0.53  fof(f100,plain,(
% 1.36/0.53    v1_funct_1(sK6(sK0,sK1,sK2))),
% 1.36/0.53    inference(resolution,[],[f50,f97])).
% 1.36/0.53  fof(f97,plain,(
% 1.36/0.53    ( ! [X6,X0,X1] : (v1_funct_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.36/0.53    inference(equality_resolution,[],[f76])).
% 1.36/0.53  fof(f76,plain,(
% 1.36/0.53    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f387,plain,(
% 1.36/0.53    v1_xboole_0(k2_relat_1(sK2))),
% 1.36/0.53    inference(resolution,[],[f385,f187])).
% 1.36/0.53  fof(f187,plain,(
% 1.36/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2))),
% 1.36/0.53    inference(subsumption_resolution,[],[f186,f137])).
% 1.36/0.53  fof(f186,plain,(
% 1.36/0.53    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | v1_xboole_0(k2_relat_1(sK2))),
% 1.36/0.53    inference(subsumption_resolution,[],[f185,f111])).
% 1.36/0.53  fof(f185,plain,(
% 1.36/0.53    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | v1_xboole_0(k2_relat_1(sK2))),
% 1.36/0.53    inference(resolution,[],[f135,f56])).
% 1.36/0.53  fof(f56,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.36/0.53    inference(flattening,[],[f20])).
% 1.36/0.53  fof(f20,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f12])).
% 1.36/0.53  fof(f12,axiom,(
% 1.36/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.36/0.53  fof(f135,plain,(
% 1.36/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 1.36/0.53    inference(forward_demodulation,[],[f134,f113])).
% 1.36/0.53  fof(f134,plain,(
% 1.36/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.36/0.53    inference(subsumption_resolution,[],[f126,f112])).
% 1.36/0.53  fof(f126,plain,(
% 1.36/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.36/0.53    inference(resolution,[],[f111,f53])).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f19])).
% 1.36/0.53  fof(f385,plain,(
% 1.36/0.53    ~v1_partfun1(sK2,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f382,f89])).
% 1.36/0.53  fof(f89,plain,(
% 1.36/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.53    inference(equality_resolution,[],[f61])).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.53    inference(flattening,[],[f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.53    inference(nnf_transformation,[],[f2])).
% 1.36/0.53  fof(f2,axiom,(
% 1.36/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.53  fof(f382,plain,(
% 1.36/0.53    ~v1_partfun1(sK2,sK0) | ~r1_tarski(sK0,sK0)),
% 1.36/0.53    inference(resolution,[],[f184,f182])).
% 1.36/0.53  fof(f182,plain,(
% 1.36/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r1_tarski(sK0,X1)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f181,f113])).
% 1.36/0.53  fof(f181,plain,(
% 1.36/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f166,f112])).
% 1.36/0.53  fof(f166,plain,(
% 1.36/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r1_tarski(k1_relat_1(sK2),X1) | ~v1_relat_1(sK2)) )),
% 1.36/0.53    inference(resolution,[],[f114,f69])).
% 1.36/0.53  fof(f69,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.36/0.53    inference(flattening,[],[f26])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.36/0.53    inference(ennf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.36/0.53  fof(f114,plain,(
% 1.36/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.36/0.53    inference(forward_demodulation,[],[f103,f101])).
% 1.36/0.53  fof(f103,plain,(
% 1.36/0.53    r1_tarski(k2_relat_1(sK6(sK0,sK1,sK2)),sK1)),
% 1.36/0.53    inference(resolution,[],[f50,f94])).
% 1.36/0.53  fof(f94,plain,(
% 1.36/0.53    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.36/0.53    inference(equality_resolution,[],[f79])).
% 1.36/0.53  fof(f79,plain,(
% 1.36/0.53    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.36/0.53    inference(cnf_transformation,[],[f49])).
% 1.36/0.53  fof(f184,plain,(
% 1.36/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(sK2,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f183,f111])).
% 1.36/0.53  fof(f183,plain,(
% 1.36/0.53    ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.53    inference(resolution,[],[f121,f73])).
% 1.36/0.53  fof(f73,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(flattening,[],[f29])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.36/0.53  fof(f121,plain,(
% 1.36/0.53    ~v1_funct_2(sK2,sK0,sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f120,f89])).
% 1.36/0.53  fof(f120,plain,(
% 1.36/0.53    ~r1_tarski(sK0,sK0) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.36/0.53    inference(forward_demodulation,[],[f119,f113])).
% 1.36/0.53  fof(f119,plain,(
% 1.36/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~r1_tarski(k1_relat_1(sK2),sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f118,f112])).
% 1.36/0.53  fof(f118,plain,(
% 1.36/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.36/0.53    inference(subsumption_resolution,[],[f117,f114])).
% 1.36/0.53  fof(f117,plain,(
% 1.36/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.36/0.53    inference(subsumption_resolution,[],[f115,f111])).
% 1.36/0.53  fof(f115,plain,(
% 1.36/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.36/0.53    inference(resolution,[],[f51,f69])).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f481,plain,(
% 1.36/0.53    ( ! [X7] : (~v1_xboole_0(X7)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f477,f386])).
% 1.36/0.53  fof(f386,plain,(
% 1.36/0.53    ~v1_xboole_0(sK0)),
% 1.36/0.53    inference(resolution,[],[f385,f201])).
% 1.36/0.53  fof(f201,plain,(
% 1.36/0.53    v1_partfun1(sK2,sK0) | ~v1_xboole_0(sK0)),
% 1.36/0.53    inference(resolution,[],[f137,f60])).
% 1.36/0.53  fof(f60,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 1.36/0.53  fof(f477,plain,(
% 1.36/0.53    ( ! [X7] : (v1_xboole_0(sK0) | ~v1_xboole_0(X7)) )),
% 1.36/0.53    inference(resolution,[],[f457,f59])).
% 1.36/0.53  fof(f457,plain,(
% 1.36/0.53    ( ! [X4] : (m1_subset_1(sK0,k1_zfmisc_1(X4))) )),
% 1.36/0.53    inference(resolution,[],[f451,f68])).
% 1.36/0.53  fof(f68,plain,(
% 1.36/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f43])).
% 1.36/0.53  fof(f43,plain,(
% 1.36/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.36/0.53    inference(nnf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.36/0.53  fof(f451,plain,(
% 1.36/0.53    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 1.36/0.53    inference(resolution,[],[f443,f151])).
% 1.36/0.53  fof(f151,plain,(
% 1.36/0.53    ( ! [X5] : (~v4_relat_1(sK2,X5) | r1_tarski(sK0,X5)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f141,f113])).
% 1.36/0.53  fof(f141,plain,(
% 1.36/0.53    ( ! [X5] : (r1_tarski(k1_relat_1(sK2),X5) | ~v4_relat_1(sK2,X5)) )),
% 1.36/0.53    inference(resolution,[],[f112,f57])).
% 1.36/0.53  fof(f57,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(nnf_transformation,[],[f22])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.36/0.53  fof(f443,plain,(
% 1.36/0.53    ( ! [X5] : (v4_relat_1(sK2,X5)) )),
% 1.36/0.53    inference(resolution,[],[f432,f70])).
% 1.36/0.53  fof(f70,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.53  fof(f432,plain,(
% 1.36/0.53    ( ! [X4] : (m1_subset_1(sK2,k1_zfmisc_1(X4))) )),
% 1.36/0.53    inference(resolution,[],[f422,f68])).
% 1.36/0.53  fof(f422,plain,(
% 1.36/0.53    ( ! [X2] : (r1_tarski(sK2,X2)) )),
% 1.36/0.53    inference(resolution,[],[f411,f65])).
% 1.36/0.53  fof(f65,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f42])).
% 1.36/0.53  fof(f42,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 1.36/0.53  fof(f41,plain,(
% 1.36/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.53    inference(rectify,[],[f39])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.53    inference(nnf_transformation,[],[f25])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f1])).
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.53  fof(f411,plain,(
% 1.36/0.53    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 1.36/0.53    inference(resolution,[],[f409,f89])).
% 1.36/0.53  fof(f409,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(resolution,[],[f406,f68])).
% 1.36/0.53  fof(f406,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~r2_hidden(X1,X0)) )),
% 1.36/0.53    inference(resolution,[],[f394,f87])).
% 1.36/0.53  fof(f87,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f33])).
% 1.36/0.53  fof(f33,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f5])).
% 1.36/0.53  fof(f5,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (20142)------------------------------
% 1.36/0.53  % (20142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (20142)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (20142)Memory used [KB]: 2046
% 1.36/0.53  % (20142)Time elapsed: 0.135 s
% 1.36/0.53  % (20142)------------------------------
% 1.36/0.53  % (20142)------------------------------
% 1.36/0.53  % (20139)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.53  % (20117)Success in time 0.186 s
%------------------------------------------------------------------------------
