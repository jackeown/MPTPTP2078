%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0963+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:58 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  119 (10489 expanded)
%              Number of leaves         :   16 (2734 expanded)
%              Depth                    :   40
%              Number of atoms          :  436 (70466 expanded)
%              Number of equality atoms :  103 (12074 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f956,plain,(
    $false ),
    inference(resolution,[],[f918,f863])).

fof(f863,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f723,f752])).

fof(f752,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f743,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f743,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f731,f58])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f731,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f726,f67])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f726,plain,(
    ! [X0] : m1_subset_1(sK0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f723,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f723,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(resolution,[],[f722,f58])).

fof(f722,plain,(
    ! [X12,X11] :
      ( ~ v1_xboole_0(X11)
      | r1_tarski(sK0,X12) ) ),
    inference(resolution,[],[f716,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f716,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f715])).

fof(f715,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f499,f59])).

fof(f499,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f134,f494])).

fof(f494,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f493,f492])).

fof(f492,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK7(sK0,sK0),sK0) ),
    inference(resolution,[],[f489,f70])).

fof(f489,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f488,f365])).

fof(f365,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(forward_demodulation,[],[f364,f55])).

fof(f55,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),sK1)
        | ~ r2_hidden(X3,sK0) )
    & sK0 = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK2,X3),sK1)
          | ~ r2_hidden(X3,sK0) )
      & sK0 = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f364,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f358,f53])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f358,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f349,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f349,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f151,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f151,plain,(
    ! [X6] :
      ( r2_hidden(sK7(k2_relat_1(sK2),X6),sK1)
      | r1_tarski(k2_relat_1(sK2),X6) ) ),
    inference(resolution,[],[f143,f70])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK2))
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f142,f112])).

fof(f112,plain,(
    ! [X8] :
      ( r2_hidden(sK5(sK2,X8),sK0)
      | ~ r2_hidden(X8,k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f111,f55])).

fof(f111,plain,(
    ! [X8] :
      ( r2_hidden(sK5(sK2,X8),k1_relat_1(sK2))
      | ~ r2_hidden(X8,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f101,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X8] :
      ( r2_hidden(sK5(sK2,X8),k1_relat_1(sK2))
      | ~ r2_hidden(X8,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f53,f89])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f142,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ r2_hidden(X1,k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f137,f54])).

fof(f137,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ r2_hidden(X1,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f88])).

fof(f88,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f488,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f487,f443])).

fof(f443,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,X2)
      | sK0 = k1_relset_1(X2,sK1,sK2) ) ),
    inference(forward_demodulation,[],[f435,f55])).

fof(f435,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,X2)
      | k1_relat_1(sK2) = k1_relset_1(X2,sK1,sK2) ) ),
    inference(resolution,[],[f365,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f487,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f480,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f480,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f476,f54])).

fof(f476,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f57,f365])).

fof(f57,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f493,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK7(sK0,sK0),sK0) ),
    inference(resolution,[],[f489,f71])).

fof(f134,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f918,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f917,f907])).

fof(f907,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f828,f752])).

fof(f828,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f637,f752])).

fof(f637,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f480,f494])).

fof(f917,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f848,f904])).

fof(f904,plain,(
    ! [X3] : k1_xboole_0 = k1_relset_1(X3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f903,f752])).

fof(f903,plain,(
    ! [X3] : sK0 = k1_relset_1(X3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f826,f878])).

fof(f878,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f757,f746])).

fof(f746,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f743,f208])).

fof(f208,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X4,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f112,f74])).

fof(f757,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | r2_hidden(k1_funct_1(sK2,X6),k2_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f109,f752])).

fof(f109,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),k2_relat_1(sK2))
      | ~ r2_hidden(X6,sK0) ) ),
    inference(forward_demodulation,[],[f108,f55])).

fof(f108,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),k2_relat_1(sK2))
      | ~ r2_hidden(X6,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f99,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),k2_relat_1(sK2))
      | ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f53,f87])).

fof(f87,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f826,plain,(
    ! [X3] :
      ( r2_hidden(sK7(k1_xboole_0,X3),k1_xboole_0)
      | sK0 = k1_relset_1(X3,k1_xboole_0,sK2) ) ),
    inference(backward_demodulation,[],[f635,f752])).

fof(f635,plain,(
    ! [X3] :
      ( sK0 = k1_relset_1(X3,k1_xboole_0,sK2)
      | r2_hidden(sK7(sK0,X3),sK0) ) ),
    inference(backward_demodulation,[],[f460,f494])).

fof(f460,plain,(
    ! [X3] :
      ( sK0 = k1_relset_1(X3,sK1,sK2)
      | r2_hidden(sK7(sK0,X3),sK0) ) ),
    inference(resolution,[],[f443,f70])).

fof(f848,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f675,f752])).

fof(f675,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f617,f494])).

fof(f617,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(backward_demodulation,[],[f438,f494])).

fof(f438,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | v1_funct_2(sK2,k1_xboole_0,sK1)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(resolution,[],[f365,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------
