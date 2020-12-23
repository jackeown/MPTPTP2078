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
% DateTime   : Thu Dec  3 12:43:53 EST 2020

% Result     : Theorem 3.09s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 622 expanded)
%              Number of leaves         :   20 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  319 (1423 expanded)
%              Number of equality atoms :   92 ( 539 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3043,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2980,f192])).

fof(f192,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f186,f191])).

fof(f191,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f80,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f61])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f44])).

fof(f44,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f186,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f81,f82])).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f81,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f2980,plain,(
    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f430,f2976])).

fof(f2976,plain,(
    sK0 = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f2968,f84])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f2968,plain,(
    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f256,f2962])).

fof(f2962,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f306,f2754])).

fof(f2754,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2732,f1118])).

fof(f1118,plain,(
    ! [X26] :
      ( r2_hidden(X26,sK1)
      | ~ r2_hidden(X26,k1_xboole_0) ) ),
    inference(superposition,[],[f182,f1042])).

fof(f1042,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[],[f144,f423])).

fof(f423,plain,(
    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f406,f238])).

fof(f238,plain,(
    sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f235,f85])).

fof(f85,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f235,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k3_subset_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f227,f106])).

fof(f227,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f220,f144])).

fof(f220,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f219,f80])).

fof(f219,plain,(
    ! [X0] :
      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f118,f189])).

fof(f189,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k7_subset_1(sK0,sK1,X2) ),
    inference(resolution,[],[f80,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f406,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,k1_xboole_0),sK1)) ),
    inference(resolution,[],[f265,f227])).

fof(f265,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,X1),sK1)) ) ),
    inference(forward_demodulation,[],[f258,f146])).

fof(f146,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f92,f97,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f258,plain,(
    ! [X1] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(k3_subset_1(sK0,X1),k4_xboole_0(sK1,k3_subset_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f188,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f188,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X1,sK1) = k5_xboole_0(X1,k4_xboole_0(sK1,X1)) ) ),
    inference(resolution,[],[f80,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f120,f97])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f144,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f89,f97])).

fof(f89,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f182,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2732,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f1117,f1054])).

fof(f1054,plain,(
    ! [X7] :
      ( r2_hidden(X7,k4_subset_1(sK0,sK0,sK1))
      | ~ r2_hidden(X7,sK1) ) ),
    inference(superposition,[],[f184,f423])).

fof(f184,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f135,f97])).

fof(f135,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1117,plain,(
    ! [X25] :
      ( ~ r2_hidden(X25,k4_subset_1(sK0,sK0,sK1))
      | ~ r2_hidden(X25,k1_xboole_0) ) ),
    inference(superposition,[],[f181,f1042])).

fof(f181,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f306,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,sK0,X1),X1)
      | k4_xboole_0(sK1,sK0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,sK0,X1),X1)
      | k4_xboole_0(sK1,sK0) = X1
      | k4_xboole_0(sK1,sK0) = X1
      | r2_hidden(sK4(sK1,sK0,X1),X1) ) ),
    inference(resolution,[],[f199,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f199,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK4(sK1,X10,X11),sK0)
      | r2_hidden(sK4(sK1,X10,X11),X11)
      | k4_xboole_0(sK1,X10) = X11 ) ),
    inference(resolution,[],[f190,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f190,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f80,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f256,plain,(
    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f188,f246])).

fof(f246,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f245,f227])).

fof(f245,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f105,f238])).

fof(f430,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f240,f429])).

fof(f429,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f428,f256])).

fof(f428,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f427,f146])).

fof(f427,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f426,f149])).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f98,f97,f97])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f426,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f408,f191])).

fof(f408,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f265,f80])).

fof(f240,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f187,f213])).

fof(f213,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f212,f80])).

fof(f212,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f105,f191])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f80,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:12:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (6900)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (6892)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6910)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (6902)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (6899)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (6894)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (6916)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (6889)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (6910)Refutation not found, incomplete strategy% (6910)------------------------------
% 0.22/0.53  % (6910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6910)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6910)Memory used [KB]: 10746
% 0.22/0.53  % (6910)Time elapsed: 0.060 s
% 0.22/0.53  % (6910)------------------------------
% 0.22/0.53  % (6910)------------------------------
% 0.22/0.53  % (6896)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (6908)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (6893)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (6907)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (6888)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (6906)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (6891)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (6895)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (6909)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (6897)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (6904)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (6914)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (6917)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (6903)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (6901)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (6898)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (6911)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (6912)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (6890)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (6905)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.58  % (6905)Refutation not found, incomplete strategy% (6905)------------------------------
% 0.22/0.58  % (6905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (6905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (6913)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (6915)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.81/0.60  % (6905)Memory used [KB]: 10618
% 1.81/0.60  % (6905)Time elapsed: 0.174 s
% 1.81/0.60  % (6905)------------------------------
% 1.81/0.60  % (6905)------------------------------
% 2.06/0.65  % (6963)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.57/0.77  % (6964)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.09/0.84  % (6893)Time limit reached!
% 3.09/0.84  % (6893)------------------------------
% 3.09/0.84  % (6893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.84  % (6893)Termination reason: Time limit
% 3.09/0.84  % (6893)Termination phase: Saturation
% 3.09/0.84  
% 3.09/0.84  % (6893)Memory used [KB]: 8699
% 3.09/0.84  % (6893)Time elapsed: 0.400 s
% 3.09/0.84  % (6893)------------------------------
% 3.09/0.84  % (6893)------------------------------
% 3.09/0.84  % (6896)Refutation found. Thanks to Tanya!
% 3.09/0.84  % SZS status Theorem for theBenchmark
% 3.09/0.84  % SZS output start Proof for theBenchmark
% 3.09/0.84  fof(f3043,plain,(
% 3.09/0.84    $false),
% 3.09/0.84    inference(subsumption_resolution,[],[f2980,f192])).
% 3.09/0.84  fof(f192,plain,(
% 3.09/0.84    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 3.09/0.84    inference(backward_demodulation,[],[f186,f191])).
% 3.09/0.84  fof(f191,plain,(
% 3.09/0.84    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 3.09/0.84    inference(resolution,[],[f80,f106])).
% 3.09/0.84  fof(f106,plain,(
% 3.09/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.09/0.84    inference(cnf_transformation,[],[f52])).
% 3.09/0.84  fof(f52,plain,(
% 3.09/0.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f38])).
% 3.09/0.84  fof(f38,axiom,(
% 3.09/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.09/0.84  fof(f80,plain,(
% 3.09/0.84    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(cnf_transformation,[],[f62])).
% 3.09/0.84  fof(f62,plain,(
% 3.09/0.84    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f61])).
% 3.09/0.84  fof(f61,plain,(
% 3.09/0.84    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.09/0.84    introduced(choice_axiom,[])).
% 3.09/0.84  fof(f48,plain,(
% 3.09/0.84    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f45])).
% 3.09/0.84  fof(f45,negated_conjecture,(
% 3.09/0.84    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.09/0.84    inference(negated_conjecture,[],[f44])).
% 3.09/0.84  fof(f44,conjecture,(
% 3.09/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 3.09/0.84  fof(f186,plain,(
% 3.09/0.84    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 3.09/0.84    inference(forward_demodulation,[],[f81,f82])).
% 3.09/0.84  fof(f82,plain,(
% 3.09/0.84    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.09/0.84    inference(cnf_transformation,[],[f37])).
% 3.09/0.84  fof(f37,axiom,(
% 3.09/0.84    ! [X0] : k2_subset_1(X0) = X0),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 3.09/0.84  fof(f81,plain,(
% 3.09/0.84    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 3.09/0.84    inference(cnf_transformation,[],[f62])).
% 3.09/0.84  fof(f2980,plain,(
% 3.09/0.84    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 3.09/0.84    inference(backward_demodulation,[],[f430,f2976])).
% 3.09/0.84  fof(f2976,plain,(
% 3.09/0.84    sK0 = k4_subset_1(sK0,sK0,sK1)),
% 3.09/0.84    inference(forward_demodulation,[],[f2968,f84])).
% 3.09/0.84  fof(f84,plain,(
% 3.09/0.84    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.09/0.84    inference(cnf_transformation,[],[f30])).
% 3.09/0.84  fof(f30,axiom,(
% 3.09/0.84    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 3.09/0.84  fof(f2968,plain,(
% 3.09/0.84    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 3.09/0.84    inference(backward_demodulation,[],[f256,f2962])).
% 3.09/0.84  fof(f2962,plain,(
% 3.09/0.84    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 3.09/0.84    inference(resolution,[],[f306,f2754])).
% 3.09/0.84  fof(f2754,plain,(
% 3.09/0.84    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.09/0.84    inference(subsumption_resolution,[],[f2732,f1118])).
% 3.09/0.84  fof(f1118,plain,(
% 3.09/0.84    ( ! [X26] : (r2_hidden(X26,sK1) | ~r2_hidden(X26,k1_xboole_0)) )),
% 3.09/0.84    inference(superposition,[],[f182,f1042])).
% 3.09/0.84  fof(f1042,plain,(
% 3.09/0.84    k1_xboole_0 = k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1))),
% 3.09/0.84    inference(superposition,[],[f144,f423])).
% 3.09/0.84  fof(f423,plain,(
% 3.09/0.84    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 3.09/0.84    inference(forward_demodulation,[],[f406,f238])).
% 3.09/0.84  fof(f238,plain,(
% 3.09/0.84    sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 3.09/0.84    inference(forward_demodulation,[],[f235,f85])).
% 3.09/0.84  fof(f85,plain,(
% 3.09/0.84    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.09/0.84    inference(cnf_transformation,[],[f19])).
% 3.09/0.84  fof(f19,axiom,(
% 3.09/0.84    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.09/0.84  fof(f235,plain,(
% 3.09/0.84    k4_xboole_0(sK0,k1_xboole_0) = k3_subset_1(sK0,k1_xboole_0)),
% 3.09/0.84    inference(resolution,[],[f227,f106])).
% 3.09/0.84  fof(f227,plain,(
% 3.09/0.84    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(superposition,[],[f220,f144])).
% 3.09/0.84  fof(f220,plain,(
% 3.09/0.84    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 3.09/0.84    inference(subsumption_resolution,[],[f219,f80])).
% 3.09/0.84  fof(f219,plain,(
% 3.09/0.84    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) )),
% 3.09/0.84    inference(superposition,[],[f118,f189])).
% 3.09/0.84  fof(f189,plain,(
% 3.09/0.84    ( ! [X2] : (k4_xboole_0(sK1,X2) = k7_subset_1(sK0,sK1,X2)) )),
% 3.09/0.84    inference(resolution,[],[f80,f119])).
% 3.09/0.84  fof(f119,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 3.09/0.84    inference(cnf_transformation,[],[f56])).
% 3.09/0.84  fof(f56,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f43])).
% 3.09/0.84  fof(f43,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.09/0.84  fof(f118,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f55])).
% 3.09/0.84  fof(f55,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f40])).
% 3.09/0.84  fof(f40,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 3.09/0.84  fof(f406,plain,(
% 3.09/0.84    k4_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,k1_xboole_0),sK1))),
% 3.09/0.84    inference(resolution,[],[f265,f227])).
% 3.09/0.84  fof(f265,plain,(
% 3.09/0.84    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,X1),sK1))) )),
% 3.09/0.84    inference(forward_demodulation,[],[f258,f146])).
% 3.09/0.84  fof(f146,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 3.09/0.84    inference(definition_unfolding,[],[f92,f97,f97])).
% 3.09/0.84  fof(f97,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f34])).
% 3.09/0.84  fof(f34,axiom,(
% 3.09/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.09/0.84  fof(f92,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.09/0.84    inference(cnf_transformation,[],[f1])).
% 3.09/0.84  fof(f1,axiom,(
% 3.09/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.09/0.84  fof(f258,plain,(
% 3.09/0.84    ( ! [X1] : (k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(k3_subset_1(sK0,X1),k4_xboole_0(sK1,k3_subset_1(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 3.09/0.84    inference(resolution,[],[f188,f105])).
% 3.09/0.84  fof(f105,plain,(
% 3.09/0.84    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f51])).
% 3.09/0.84  fof(f51,plain,(
% 3.09/0.84    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f39])).
% 3.09/0.84  fof(f39,axiom,(
% 3.09/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.09/0.84  fof(f188,plain,(
% 3.09/0.84    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X1,sK1) = k5_xboole_0(X1,k4_xboole_0(sK1,X1))) )),
% 3.09/0.84    inference(resolution,[],[f80,f164])).
% 3.09/0.84  fof(f164,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.84    inference(definition_unfolding,[],[f120,f97])).
% 3.09/0.84  fof(f120,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f58])).
% 3.09/0.84  fof(f58,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(flattening,[],[f57])).
% 3.09/0.84  fof(f57,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.09/0.84    inference(ennf_transformation,[],[f42])).
% 3.09/0.84  fof(f42,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.09/0.84  fof(f144,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 3.09/0.84    inference(definition_unfolding,[],[f89,f97])).
% 3.09/0.84  fof(f89,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f22])).
% 3.09/0.84  fof(f22,axiom,(
% 3.09/0.84    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.09/0.84  fof(f182,plain,(
% 3.09/0.84    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 3.09/0.84    inference(equality_resolution,[],[f128])).
% 3.09/0.84  fof(f128,plain,(
% 3.09/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.09/0.84    inference(cnf_transformation,[],[f74])).
% 3.09/0.84  fof(f74,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f72,f73])).
% 3.09/0.84  fof(f73,plain,(
% 3.09/0.84    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.09/0.84    introduced(choice_axiom,[])).
% 3.09/0.84  fof(f72,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(rectify,[],[f71])).
% 3.09/0.84  fof(f71,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(flattening,[],[f70])).
% 3.09/0.84  fof(f70,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(nnf_transformation,[],[f6])).
% 3.09/0.84  fof(f6,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.09/0.84  fof(f2732,plain,(
% 3.09/0.84    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK1)) )),
% 3.09/0.84    inference(resolution,[],[f1117,f1054])).
% 3.09/0.84  fof(f1054,plain,(
% 3.09/0.84    ( ! [X7] : (r2_hidden(X7,k4_subset_1(sK0,sK0,sK1)) | ~r2_hidden(X7,sK1)) )),
% 3.09/0.84    inference(superposition,[],[f184,f423])).
% 3.09/0.84  fof(f184,plain,(
% 3.09/0.84    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 3.09/0.84    inference(equality_resolution,[],[f175])).
% 3.09/0.84  fof(f175,plain,(
% 3.09/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 3.09/0.84    inference(definition_unfolding,[],[f135,f97])).
% 3.09/0.84  fof(f135,plain,(
% 3.09/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.09/0.84    inference(cnf_transformation,[],[f79])).
% 3.09/0.84  fof(f79,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f77,f78])).
% 3.09/0.84  fof(f78,plain,(
% 3.09/0.84    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 3.09/0.84    introduced(choice_axiom,[])).
% 3.09/0.84  fof(f77,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(rectify,[],[f76])).
% 3.09/0.84  fof(f76,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(flattening,[],[f75])).
% 3.09/0.84  fof(f75,plain,(
% 3.09/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.09/0.84    inference(nnf_transformation,[],[f4])).
% 3.09/0.84  fof(f4,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.09/0.84  fof(f1117,plain,(
% 3.09/0.84    ( ! [X25] : (~r2_hidden(X25,k4_subset_1(sK0,sK0,sK1)) | ~r2_hidden(X25,k1_xboole_0)) )),
% 3.09/0.84    inference(superposition,[],[f181,f1042])).
% 3.09/0.84  fof(f181,plain,(
% 3.09/0.84    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.09/0.84    inference(equality_resolution,[],[f129])).
% 3.09/0.84  fof(f129,plain,(
% 3.09/0.84    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.09/0.84    inference(cnf_transformation,[],[f74])).
% 3.09/0.84  fof(f306,plain,(
% 3.09/0.84    ( ! [X1] : (r2_hidden(sK4(sK1,sK0,X1),X1) | k4_xboole_0(sK1,sK0) = X1) )),
% 3.09/0.84    inference(duplicate_literal_removal,[],[f293])).
% 3.09/0.84  fof(f293,plain,(
% 3.09/0.84    ( ! [X1] : (r2_hidden(sK4(sK1,sK0,X1),X1) | k4_xboole_0(sK1,sK0) = X1 | k4_xboole_0(sK1,sK0) = X1 | r2_hidden(sK4(sK1,sK0,X1),X1)) )),
% 3.09/0.84    inference(resolution,[],[f199,f132])).
% 3.09/0.84  fof(f132,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.09/0.84    inference(cnf_transformation,[],[f74])).
% 3.09/0.84  fof(f199,plain,(
% 3.09/0.84    ( ! [X10,X11] : (r2_hidden(sK4(sK1,X10,X11),sK0) | r2_hidden(sK4(sK1,X10,X11),X11) | k4_xboole_0(sK1,X10) = X11) )),
% 3.09/0.84    inference(resolution,[],[f190,f131])).
% 3.09/0.84  fof(f131,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 3.09/0.84    inference(cnf_transformation,[],[f74])).
% 3.09/0.84  fof(f190,plain,(
% 3.09/0.84    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,sK0)) )),
% 3.09/0.84    inference(resolution,[],[f80,f107])).
% 3.09/0.84  fof(f107,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 3.09/0.84    inference(cnf_transformation,[],[f53])).
% 3.09/0.84  fof(f53,plain,(
% 3.09/0.84    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(ennf_transformation,[],[f41])).
% 3.09/0.84  fof(f41,axiom,(
% 3.09/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 3.09/0.84  fof(f256,plain,(
% 3.09/0.84    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 3.09/0.84    inference(resolution,[],[f188,f246])).
% 3.09/0.84  fof(f246,plain,(
% 3.09/0.84    m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(subsumption_resolution,[],[f245,f227])).
% 3.09/0.84  fof(f245,plain,(
% 3.09/0.84    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(superposition,[],[f105,f238])).
% 3.09/0.84  fof(f430,plain,(
% 3.09/0.84    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)),
% 3.09/0.84    inference(backward_demodulation,[],[f240,f429])).
% 3.09/0.84  fof(f429,plain,(
% 3.09/0.84    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_subset_1(sK0,sK0,sK1)),
% 3.09/0.84    inference(forward_demodulation,[],[f428,f256])).
% 3.09/0.84  fof(f428,plain,(
% 3.09/0.84    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 3.09/0.84    inference(forward_demodulation,[],[f427,f146])).
% 3.09/0.84  fof(f427,plain,(
% 3.09/0.84    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 3.09/0.84    inference(forward_demodulation,[],[f426,f149])).
% 3.09/0.84  fof(f149,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 3.09/0.84    inference(definition_unfolding,[],[f98,f97,f97])).
% 3.09/0.84  fof(f98,plain,(
% 3.09/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f18])).
% 3.09/0.84  fof(f18,axiom,(
% 3.09/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.09/0.84  fof(f426,plain,(
% 3.09/0.84    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 3.09/0.84    inference(forward_demodulation,[],[f408,f191])).
% 3.09/0.84  fof(f408,plain,(
% 3.09/0.84    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(sK1,k4_xboole_0(k3_subset_1(sK0,sK1),sK1))),
% 3.09/0.84    inference(resolution,[],[f265,f80])).
% 3.09/0.84  fof(f240,plain,(
% 3.09/0.84    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)),
% 3.09/0.84    inference(resolution,[],[f187,f213])).
% 3.09/0.84  fof(f213,plain,(
% 3.09/0.84    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(subsumption_resolution,[],[f212,f80])).
% 3.09/0.84  fof(f212,plain,(
% 3.09/0.84    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.09/0.84    inference(superposition,[],[f105,f191])).
% 3.09/0.84  fof(f187,plain,(
% 3.09/0.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)) )),
% 3.09/0.84    inference(resolution,[],[f80,f121])).
% 3.09/0.84  fof(f121,plain,(
% 3.09/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.84    inference(cnf_transformation,[],[f60])).
% 3.09/0.84  fof(f60,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.84    inference(flattening,[],[f59])).
% 3.09/0.84  fof(f59,plain,(
% 3.09/0.84    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.09/0.84    inference(ennf_transformation,[],[f36])).
% 3.09/0.84  fof(f36,axiom,(
% 3.09/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 3.09/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 3.09/0.84  % SZS output end Proof for theBenchmark
% 3.09/0.84  % (6896)------------------------------
% 3.09/0.84  % (6896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.84  % (6896)Termination reason: Refutation
% 3.09/0.84  
% 3.09/0.84  % (6896)Memory used [KB]: 12920
% 3.09/0.84  % (6896)Time elapsed: 0.428 s
% 3.09/0.84  % (6896)------------------------------
% 3.09/0.84  % (6896)------------------------------
% 3.09/0.85  % (6883)Success in time 0.476 s
%------------------------------------------------------------------------------
