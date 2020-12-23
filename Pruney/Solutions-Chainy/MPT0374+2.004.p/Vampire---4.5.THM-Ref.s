%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:32 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 227 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   21
%              Number of atoms          :  350 (1094 expanded)
%              Number of equality atoms :   98 ( 285 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f58,f417,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f417,plain,(
    ! [X5] : ~ r1_tarski(X5,sK0) ),
    inference(subsumption_resolution,[],[f412,f130])).

fof(f130,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f127,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f101,f58])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,k1_tarski(X1)) ) ),
    inference(superposition,[],[f102,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(resolution,[],[f82,f96])).

fof(f96,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f412,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_xboole_0)
      | ~ r1_tarski(X5,sK0) ) ),
    inference(superposition,[],[f98,f394])).

fof(f394,plain,(
    k1_xboole_0 = k1_zfmisc_1(sK0) ),
    inference(resolution,[],[f391,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f391,plain,(
    v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f390])).

fof(f390,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f111,f384])).

fof(f384,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f298,f293])).

fof(f293,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f288,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X2,sK0) )
   => ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

% (26102)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f288,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f263,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f262,f93])).

fof(f93,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f57,f92])).

fof(f92,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f258,f130])).

fof(f258,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,k3_subset_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f298,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,sK2),sK0) ) ),
    inference(resolution,[],[f294,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f294,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f289,f54])).

fof(f289,plain,
    ( r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f263,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f106,f79])).

fof(f106,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f105,f98])).

fof(f105,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f98,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

% (26102)Refutation not found, incomplete strategy% (26102)------------------------------
% (26102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26102)Termination reason: Refutation not found, incomplete strategy

% (26102)Memory used [KB]: 10746
% (26102)Time elapsed: 0.158 s
% (26102)------------------------------
% (26102)------------------------------
fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:42:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (26094)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (26120)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (26096)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (26104)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (26104)Refutation not found, incomplete strategy% (26104)------------------------------
% 0.21/0.52  % (26104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26120)Refutation not found, incomplete strategy% (26120)------------------------------
% 0.21/0.52  % (26120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26092)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (26104)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26104)Memory used [KB]: 10618
% 0.21/0.52  % (26104)Time elapsed: 0.116 s
% 0.21/0.52  % (26104)------------------------------
% 0.21/0.52  % (26104)------------------------------
% 0.21/0.53  % (26111)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26120)Memory used [KB]: 10746
% 0.21/0.53  % (26120)Time elapsed: 0.116 s
% 0.21/0.53  % (26120)------------------------------
% 0.21/0.53  % (26120)------------------------------
% 0.21/0.53  % (26112)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (26114)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (26119)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (26119)Refutation not found, incomplete strategy% (26119)------------------------------
% 0.21/0.54  % (26119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26119)Memory used [KB]: 6140
% 0.21/0.54  % (26119)Time elapsed: 0.132 s
% 0.21/0.54  % (26119)------------------------------
% 0.21/0.54  % (26119)------------------------------
% 0.21/0.54  % (26099)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (26097)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26107)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.55  % (26105)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.55  % (26092)Refutation not found, incomplete strategy% (26092)------------------------------
% 1.43/0.55  % (26092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (26092)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (26092)Memory used [KB]: 1663
% 1.43/0.55  % (26092)Time elapsed: 0.132 s
% 1.43/0.55  % (26092)------------------------------
% 1.43/0.55  % (26092)------------------------------
% 1.43/0.55  % (26091)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.55  % (26093)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.43/0.55  % (26095)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.55  % (26101)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.55  % (26108)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.56  % (26115)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.56  % (26121)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.56  % (26121)Refutation not found, incomplete strategy% (26121)------------------------------
% 1.43/0.56  % (26121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (26121)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (26121)Memory used [KB]: 1663
% 1.43/0.56  % (26121)Time elapsed: 0.001 s
% 1.43/0.56  % (26121)------------------------------
% 1.43/0.56  % (26121)------------------------------
% 1.43/0.56  % (26100)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.56  % (26113)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.56  % (26103)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (26106)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.56  % (26110)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.56  % (26109)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.56  % (26108)Refutation not found, incomplete strategy% (26108)------------------------------
% 1.55/0.56  % (26108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (26108)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (26108)Memory used [KB]: 10746
% 1.55/0.56  % (26108)Time elapsed: 0.156 s
% 1.55/0.56  % (26108)------------------------------
% 1.55/0.56  % (26108)------------------------------
% 1.55/0.56  % (26110)Refutation not found, incomplete strategy% (26110)------------------------------
% 1.55/0.56  % (26110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (26110)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (26110)Memory used [KB]: 1663
% 1.55/0.56  % (26110)Time elapsed: 0.159 s
% 1.55/0.56  % (26110)------------------------------
% 1.55/0.56  % (26110)------------------------------
% 1.55/0.56  % (26118)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.56  % (26114)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f425,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f58,f417,f79])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f43])).
% 1.55/0.57  fof(f43,plain,(
% 1.55/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.55/0.57    inference(nnf_transformation,[],[f2])).
% 1.55/0.57  fof(f2,axiom,(
% 1.55/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.55/0.57  fof(f417,plain,(
% 1.55/0.57    ( ! [X5] : (~r1_tarski(X5,sK0)) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f412,f130])).
% 1.55/0.57  fof(f130,plain,(
% 1.55/0.57    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f127,f114])).
% 1.55/0.57  fof(f114,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.55/0.57    inference(superposition,[],[f101,f58])).
% 1.55/0.57  fof(f101,plain,(
% 1.55/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.55/0.57    inference(equality_resolution,[],[f84])).
% 1.55/0.57  fof(f84,plain,(
% 1.55/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.57    inference(cnf_transformation,[],[f49])).
% 1.55/0.57  fof(f49,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 1.55/0.57  fof(f48,plain,(
% 1.55/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f47,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(rectify,[],[f46])).
% 1.55/0.57  fof(f46,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(flattening,[],[f45])).
% 1.55/0.57  fof(f45,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(nnf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.55/0.57  fof(f127,plain,(
% 1.55/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,k1_tarski(X1))) )),
% 1.55/0.57    inference(superposition,[],[f102,f123])).
% 1.55/0.57  fof(f123,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.55/0.57    inference(resolution,[],[f82,f96])).
% 1.55/0.57  fof(f96,plain,(
% 1.55/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.55/0.57    inference(equality_resolution,[],[f95])).
% 1.55/0.57  fof(f95,plain,(
% 1.55/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.55/0.57    inference(equality_resolution,[],[f72])).
% 1.55/0.57  fof(f72,plain,(
% 1.55/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f38])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.55/0.57  fof(f37,plain,(
% 1.55/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f36,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(rectify,[],[f35])).
% 1.55/0.57  fof(f35,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.57    inference(nnf_transformation,[],[f6])).
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.57  fof(f82,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f44])).
% 1.55/0.57  fof(f44,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.55/0.57    inference(nnf_transformation,[],[f9])).
% 1.55/0.57  fof(f9,axiom,(
% 1.55/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.55/0.57  fof(f102,plain,(
% 1.55/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.55/0.57    inference(equality_resolution,[],[f83])).
% 1.55/0.57  fof(f83,plain,(
% 1.55/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.57    inference(cnf_transformation,[],[f49])).
% 1.55/0.57  fof(f412,plain,(
% 1.55/0.57    ( ! [X5] : (r2_hidden(X5,k1_xboole_0) | ~r1_tarski(X5,sK0)) )),
% 1.55/0.57    inference(superposition,[],[f98,f394])).
% 1.55/0.57  fof(f394,plain,(
% 1.55/0.57    k1_xboole_0 = k1_zfmisc_1(sK0)),
% 1.55/0.57    inference(resolution,[],[f391,f61])).
% 1.55/0.57  fof(f61,plain,(
% 1.55/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.55/0.57    inference(ennf_transformation,[],[f5])).
% 1.55/0.57  fof(f5,axiom,(
% 1.55/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 1.55/0.57  fof(f391,plain,(
% 1.55/0.57    v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(trivial_inequality_removal,[],[f390])).
% 1.55/0.57  fof(f390,plain,(
% 1.55/0.57    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(backward_demodulation,[],[f111,f384])).
% 1.55/0.57  fof(f384,plain,(
% 1.55/0.57    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK2),sK0)),
% 1.55/0.57    inference(resolution,[],[f298,f293])).
% 1.55/0.57  fof(f293,plain,(
% 1.55/0.57    r2_hidden(sK1,sK0)),
% 1.55/0.57    inference(subsumption_resolution,[],[f288,f54])).
% 1.55/0.57  fof(f54,plain,(
% 1.55/0.57    k1_xboole_0 != sK0),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f32,f31])).
% 1.55/0.57  fof(f31,plain,(
% 1.55/0.57    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f32,plain,(
% 1.55/0.57    ? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) => (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f22,plain,(
% 1.55/0.57    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.55/0.57    inference(flattening,[],[f21])).
% 1.55/0.57  fof(f21,plain,(
% 1.55/0.57    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.55/0.57    inference(ennf_transformation,[],[f20])).
% 1.55/0.57  fof(f20,negated_conjecture,(
% 1.55/0.57    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 1.55/0.57    inference(negated_conjecture,[],[f19])).
% 1.55/0.57  % (26102)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.57  fof(f19,conjecture,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).
% 1.55/0.57  fof(f288,plain,(
% 1.55/0.57    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 1.55/0.57    inference(resolution,[],[f263,f52])).
% 1.55/0.57  fof(f52,plain,(
% 1.55/0.57    m1_subset_1(sK1,sK0)),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f263,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1) )),
% 1.55/0.57    inference(forward_demodulation,[],[f262,f93])).
% 1.55/0.57  fof(f93,plain,(
% 1.55/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.55/0.57    inference(definition_unfolding,[],[f57,f92])).
% 1.55/0.57  fof(f92,plain,(
% 1.55/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f60,f56])).
% 1.55/0.57  fof(f56,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f12])).
% 1.55/0.57  fof(f12,axiom,(
% 1.55/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.55/0.57  fof(f60,plain,(
% 1.55/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f16])).
% 1.55/0.57  fof(f16,axiom,(
% 1.55/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.55/0.57  fof(f57,plain,(
% 1.55/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f13])).
% 1.55/0.57  fof(f13,axiom,(
% 1.55/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.55/0.57  fof(f262,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0)) | k1_xboole_0 = X1) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f258,f130])).
% 1.55/0.57  fof(f258,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X0,X1) | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0)) | k1_xboole_0 = X1) )),
% 1.55/0.57    inference(resolution,[],[f62,f94])).
% 1.55/0.57  fof(f94,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(definition_unfolding,[],[f59,f56])).
% 1.55/0.57  fof(f59,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f14])).
% 1.55/0.57  fof(f14,axiom,(
% 1.55/0.57    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.55/0.57  fof(f62,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | r2_hidden(X2,k3_subset_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.55/0.57    inference(flattening,[],[f24])).
% 1.55/0.57  fof(f24,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.55/0.57    inference(ennf_transformation,[],[f17])).
% 1.55/0.57  fof(f17,axiom,(
% 1.55/0.57    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.55/0.57  fof(f298,plain,(
% 1.55/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,sK2),sK0)) )),
% 1.55/0.57    inference(resolution,[],[f294,f91])).
% 1.55/0.57  fof(f91,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f51])).
% 1.55/0.57  fof(f51,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.55/0.57    inference(flattening,[],[f50])).
% 1.55/0.57  fof(f50,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.55/0.57    inference(nnf_transformation,[],[f10])).
% 1.55/0.57  fof(f10,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.55/0.57  fof(f294,plain,(
% 1.55/0.57    r2_hidden(sK2,sK0)),
% 1.55/0.57    inference(subsumption_resolution,[],[f289,f54])).
% 1.55/0.57  fof(f289,plain,(
% 1.55/0.57    r2_hidden(sK2,sK0) | k1_xboole_0 = sK0),
% 1.55/0.57    inference(resolution,[],[f263,f53])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    m1_subset_1(sK2,sK0)),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f111,plain,(
% 1.55/0.57    k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(resolution,[],[f106,f79])).
% 1.55/0.57  fof(f106,plain,(
% 1.55/0.57    ~r1_tarski(k2_tarski(sK1,sK2),sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(resolution,[],[f105,f98])).
% 1.55/0.57  fof(f105,plain,(
% 1.55/0.57    ~r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(resolution,[],[f65,f55])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f34])).
% 1.55/0.57  fof(f34,plain,(
% 1.55/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.55/0.57    inference(nnf_transformation,[],[f26])).
% 1.55/0.57  fof(f26,plain,(
% 1.55/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f11])).
% 1.55/0.57  fof(f11,axiom,(
% 1.55/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.55/0.57  fof(f98,plain,(
% 1.55/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.55/0.57    inference(equality_resolution,[],[f76])).
% 1.55/0.57  fof(f76,plain,(
% 1.55/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f42])).
% 1.55/0.57  fof(f42,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.55/0.57  % (26102)Refutation not found, incomplete strategy% (26102)------------------------------
% 1.55/0.57  % (26102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (26102)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (26102)Memory used [KB]: 10746
% 1.55/0.57  % (26102)Time elapsed: 0.158 s
% 1.55/0.57  % (26102)------------------------------
% 1.55/0.57  % (26102)------------------------------
% 1.55/0.57  fof(f41,plain,(
% 1.55/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f40,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.57    inference(rectify,[],[f39])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.57    inference(nnf_transformation,[],[f7])).
% 1.55/0.57  fof(f7,axiom,(
% 1.55/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.55/0.57  fof(f58,plain,(
% 1.55/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (26114)------------------------------
% 1.55/0.57  % (26114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (26114)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (26114)Memory used [KB]: 6652
% 1.55/0.57  % (26114)Time elapsed: 0.055 s
% 1.55/0.57  % (26114)------------------------------
% 1.55/0.57  % (26114)------------------------------
% 1.55/0.57  % (26085)Success in time 0.206 s
%------------------------------------------------------------------------------
