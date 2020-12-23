%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t32_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  116 (1154 expanded)
%              Number of leaves         :   18 ( 325 expanded)
%              Depth                    :   22
%              Number of atoms          :  370 (5815 expanded)
%              Number of equality atoms :   22 ( 483 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26671,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25858,f6129])).

fof(f6129,plain,(
    m1_subset_1(sK5(sK0),k1_zfmisc_1(sK5(sK0))) ),
    inference(resolution,[],[f4472,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t3_subset)).

fof(f4472,plain,(
    r1_tarski(sK5(sK0),sK5(sK0)) ),
    inference(subsumption_resolution,[],[f4471,f1317])).

fof(f1317,plain,(
    v3_ordinal1(sK5(sK0)) ),
    inference(resolution,[],[f882,f252])).

fof(f252,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v3_ordinal1(sK5(sK0)) ) ),
    inference(resolution,[],[f207,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f62])).

fof(f62,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t7_tarski)).

fof(f207,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f202,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f111,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t5_subset)).

fof(f111,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f65,f89])).

fof(f65,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),X0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t32_ordinal1)).

fof(f202,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f130,f127])).

fof(f127,plain,(
    ! [X1] :
      ( m1_subset_1(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f111,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t4_subset)).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK1)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t2_subset)).

fof(f102,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | v3_ordinal1(X2) ) ),
    inference(resolution,[],[f64,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t23_ordinal1)).

fof(f64,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f882,plain,(
    r2_hidden(sK2(o_1_0_ordinal1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f874,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f874,plain,
    ( r2_hidden(sK2(o_1_0_ordinal1(sK0)),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f413,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t6_boole)).

fof(f413,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2(o_1_0_ordinal1(sK0)),sK0) ),
    inference(resolution,[],[f222,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(o_1_0_ordinal1(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(o_1_0_ordinal1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',dt_o_1_0_ordinal1)).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | r2_hidden(sK2(X0),sK0) ) ),
    inference(resolution,[],[f182,f81])).

fof(f182,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(sK2(X3),sK0) ) ),
    inference(subsumption_resolution,[],[f181,f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f175,f126])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f127,f81])).

fof(f181,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3),sK0)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f116,f64])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(sK2(X0),sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f68,f80])).

fof(f68,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | r2_hidden(sK2(X2),sK0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4471,plain,
    ( r1_tarski(sK5(sK0),sK5(sK0))
    | ~ v3_ordinal1(sK5(sK0)) ),
    inference(duplicate_literal_removal,[],[f4470])).

fof(f4470,plain,
    ( r1_tarski(sK5(sK0),sK5(sK0))
    | ~ v3_ordinal1(sK5(sK0))
    | ~ v3_ordinal1(sK5(sK0)) ),
    inference(resolution,[],[f1556,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',redefinition_r1_ordinal1)).

fof(f1556,plain,(
    r1_ordinal1(sK5(sK0),sK5(sK0)) ),
    inference(resolution,[],[f1317,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X0) ) ),
    inference(condensation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',reflexivity_r1_ordinal1)).

fof(f25858,plain,(
    ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(sK5(sK0))) ),
    inference(backward_demodulation,[],[f25737,f2332])).

fof(f2332,plain,(
    ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(sK2(sK5(sK0)))) ),
    inference(resolution,[],[f1331,f308])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2(X0))) ) ),
    inference(resolution,[],[f237,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2(X0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f236,f207])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_tarski(X0,sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f233,f179])).

fof(f179,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v3_ordinal1(sK2(X3)) ) ),
    inference(subsumption_resolution,[],[f178,f176])).

fof(f178,plain,(
    ! [X3] :
      ( v3_ordinal1(sK2(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f114,f64])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | v3_ordinal1(sK2(X0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f67,f80])).

fof(f67,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | v3_ordinal1(sK2(X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_tarski(X0,sK2(X0))
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f185,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f185,plain,(
    ! [X3] :
      ( ~ r1_ordinal1(X3,sK2(X3))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f184,f176])).

fof(f184,plain,(
    ! [X3] :
      ( ~ r1_ordinal1(X3,sK2(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f118,f64])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,sK2(X0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f69,f80])).

fof(f69,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | ~ r1_ordinal1(X2,sK2(X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1331,plain,(
    r2_hidden(sK5(sK0),sK0) ),
    inference(resolution,[],[f882,f92])).

fof(f25737,plain,(
    sK2(sK5(sK0)) = sK5(sK0) ),
    inference(resolution,[],[f3413,f4039])).

fof(f4039,plain,(
    ~ r2_hidden(sK2(sK5(sK0)),sK5(sK0)) ),
    inference(resolution,[],[f1314,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK5(X1)) ) ),
    inference(condensation,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1314,plain,(
    r2_hidden(sK2(sK5(sK0)),sK0) ),
    inference(resolution,[],[f882,f226])).

fof(f226,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(sK2(sK5(sK0)),sK0) ) ),
    inference(resolution,[],[f182,f92])).

fof(f3413,plain,
    ( r2_hidden(sK2(sK5(sK0)),sK5(sK0))
    | sK2(sK5(sK0)) = sK5(sK0) ),
    inference(resolution,[],[f1027,f1331])).

fof(f1027,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK2(X1),X1)
      | sK2(X1) = X1 ) ),
    inference(subsumption_resolution,[],[f1026,f207])).

fof(f1026,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK2(X1),X1)
      | sK2(X1) = X1
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f1025,f179])).

fof(f1025,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK2(X1),X1)
      | sK2(X1) = X1
      | ~ v3_ordinal1(sK2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f1023,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',cc1_ordinal1)).

fof(f1023,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_ordinal1(sK2(X1))
      | r2_hidden(sK2(X1),X1)
      | sK2(X1) = X1
      | ~ v3_ordinal1(sK2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f310,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',t24_ordinal1)).

fof(f310,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v1_ordinal1(sK2(X2)) ) ),
    inference(resolution,[],[f237,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t32_ordinal1.p',d2_ordinal1)).
%------------------------------------------------------------------------------
