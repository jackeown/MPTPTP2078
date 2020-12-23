%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0431+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 141 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 ( 816 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8653,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8377,f2306])).

fof(f2306,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f1561,f1726,f1451])).

fof(f1451,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1095])).

fof(f1095,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f918])).

fof(f918,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK18(X0,X1,X2),X1)
              & ~ r2_hidden(sK18(X0,X1,X2),X0) )
            | ~ r2_hidden(sK18(X0,X1,X2),X2) )
          & ( r2_hidden(sK18(X0,X1,X2),X1)
            | r2_hidden(sK18(X0,X1,X2),X0)
            | r2_hidden(sK18(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f916,f917])).

fof(f917,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK18(X0,X1,X2),X1)
            & ~ r2_hidden(sK18(X0,X1,X2),X0) )
          | ~ r2_hidden(sK18(X0,X1,X2),X2) )
        & ( r2_hidden(sK18(X0,X1,X2),X1)
          | r2_hidden(sK18(X0,X1,X2),X0)
          | r2_hidden(sK18(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f916,plain,(
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
    inference(rectify,[],[f915])).

fof(f915,plain,(
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
    inference(flattening,[],[f914])).

fof(f914,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1726,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f997,f998,f1038])).

fof(f1038,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_setfam_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f891])).

fof(f891,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f674])).

fof(f674,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f551])).

fof(f551,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f998,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f865])).

fof(f865,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f643,f864,f863,f862])).

fof(f862,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
              & v3_setfam_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f863,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
            & v3_setfam_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v3_setfam_1(X1,sK0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f864,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v3_setfam_1(X2,sK0) )
   => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f643,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f642])).

fof(f642,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f634])).

fof(f634,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f633])).

fof(f633,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f997,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f865])).

fof(f1561,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f995,f996,f1038])).

fof(f996,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f865])).

fof(f995,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f865])).

fof(f8377,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f1849,f1847,f1039])).

fof(f1039,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f891])).

fof(f1847,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f1766,f1754])).

fof(f1754,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f996,f998,f1001])).

fof(f1001,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f647])).

fof(f647,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f646])).

fof(f646,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1766,plain,(
    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f996,f998,f1002])).

fof(f1002,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f649])).

fof(f649,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f648])).

fof(f648,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f467])).

fof(f467,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1849,plain,(
    ~ v3_setfam_1(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f999,f1754])).

fof(f999,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f865])).
%------------------------------------------------------------------------------
