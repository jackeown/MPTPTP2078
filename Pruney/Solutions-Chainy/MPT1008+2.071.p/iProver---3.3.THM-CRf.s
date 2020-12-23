%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:19 EST 2020

% Result     : Theorem 31.40s
% Output     : CNFRefutation 31.40s
% Verified   : 
% Statistics : Number of formulae       :  231 (1310 expanded)
%              Number of clauses        :  135 ( 429 expanded)
%              Number of leaves         :   31 ( 285 expanded)
%              Depth                    :   19
%              Number of atoms          :  650 (5516 expanded)
%              Number of equality atoms :  336 (2607 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f76,plain,(
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
    inference(rectify,[],[f75])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f76,f77])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f173,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f70,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f71,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f103,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13)
      & k1_xboole_0 != sK12
      & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
      & v1_funct_2(sK13,k1_tarski(sK11),sK12)
      & v1_funct_1(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,
    ( k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13)
    & k1_xboole_0 != sK12
    & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    & v1_funct_2(sK13,k1_tarski(sK11),sK12)
    & v1_funct_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f71,f103])).

fof(f170,plain,(
    k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(cnf_transformation,[],[f104])).

fof(f166,plain,(
    v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f104])).

fof(f167,plain,(
    v1_funct_2(sK13,k1_tarski(sK11),sK12) ),
    inference(cnf_transformation,[],[f104])).

fof(f168,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) ),
    inference(cnf_transformation,[],[f104])).

fof(f169,plain,(
    k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f104])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f68])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f171,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f111])).

fof(f172,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f171])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f66])).

fof(f101,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK10(X0,X2,X3)) = X2
        & r2_hidden(sK10(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK10(X0,X2,X3)) = X2
        & r2_hidden(sK10(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f67,f101])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK10(X0,X2,X3)) = X2
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f79])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f175,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f174,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f116])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f73])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f60])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f81])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f137,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1025,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f173])).

cnf(c_11014,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k1_tarski(X1))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1025,c_8])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | sK1(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1032,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9129,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK1(X0,X1))
    | k1_tarski(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_1032])).

cnf(c_61,negated_conjecture,
    ( k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_79076,plain,
    ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | ~ v1_relat_1(k1_funct_1(sK13,sK11))
    | v1_relat_1(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))) ),
    inference(resolution,[status(thm)],[c_9129,c_61])).

cnf(c_65,negated_conjecture,
    ( v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_64,negated_conjecture,
    ( v1_funct_2(sK13,k1_tarski(sK11),sK12) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_63,negated_conjecture,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_62,negated_conjecture,
    ( k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f169])).

cnf(c_2868,plain,
    ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_60,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f165])).

cnf(c_2955,plain,
    ( ~ v1_funct_2(sK13,X0,X1)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK13,X2),k2_relset_1(X0,X1,sK13))
    | ~ v1_funct_1(sK13)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_3237,plain,
    ( ~ v1_funct_2(sK13,k1_tarski(X0),X1)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
    | ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(k1_funct_1(sK13,X0),k2_relset_1(k1_tarski(X0),X1,sK13))
    | ~ v1_funct_1(sK13)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_4204,plain,
    ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    | r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | ~ r2_hidden(sK11,k1_tarski(sK11))
    | ~ v1_funct_1(sK13)
    | k1_xboole_0 = sK12 ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_4821,plain,
    ( r2_hidden(sK11,k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3552,plain,
    ( ~ r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(X0))
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4953,plain,
    ( ~ r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_3552])).

cnf(c_4954,plain,
    ( r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4431,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X3),X3)
    | X3 != X1
    | sK1(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_8630,plain,
    ( ~ r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | r2_hidden(sK1(X0,X1),X1)
    | X1 != k2_relset_1(k1_tarski(sK11),sK12,sK13)
    | sK1(X0,X1) != k1_funct_1(sK13,sK11) ),
    inference(instantiation,[status(thm)],[c_4431])).

cnf(c_23126,plain,
    ( ~ r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relset_1(k1_tarski(sK11),sK12,sK13)
    | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_funct_1(sK13,sK11) ),
    inference(instantiation,[status(thm)],[c_8630])).

cnf(c_80073,plain,
    ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79076,c_65,c_64,c_63,c_62,c_61,c_2868,c_4204,c_4821,c_4953,c_4954,c_23126])).

cnf(c_58,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK10(X1,X3,X0)) = X3 ),
    inference(cnf_transformation,[],[f164])).

cnf(c_80086,plain,
    ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    | ~ v1_funct_1(sK13)
    | k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
    inference(resolution,[status(thm)],[c_80073,c_58])).

cnf(c_62021,plain,
    ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | ~ v1_funct_1(sK13)
    | k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_80636,plain,
    ( k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_80086,c_65,c_64,c_63,c_62,c_61,c_2868,c_4204,c_4821,c_4953,c_4954,c_23126,c_62021])).

cnf(c_82978,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
    | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X1) ),
    inference(resolution,[status(thm)],[c_11014,c_80636])).

cnf(c_88551,plain,
    ( ~ r2_hidden(X0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
    | r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
    | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(resolution,[status(thm)],[c_82978,c_6])).

cnf(c_88561,plain,
    ( r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
    | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_88551])).

cnf(c_2165,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5572,plain,
    ( r1_tarski(sK13,k2_zfmisc_1(k1_tarski(sK11),sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_2203])).

cnf(c_27,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2193,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14516,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_2193])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_176,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_34150,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14516,c_176])).

cnf(c_34151,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_34150])).

cnf(c_34159,plain,
    ( k1_tarski(sK11) = k1_xboole_0
    | sK12 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_5572,c_34151])).

cnf(c_68,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_200,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f175])).

cnf(c_201,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_56,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_2766,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    | v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_2767,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) != iProver_top
    | v1_relat_1(sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2766])).

cnf(c_1023,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2849,plain,
    ( sK12 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK12 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_2850,plain,
    ( sK12 != k1_xboole_0
    | k1_xboole_0 = sK12
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_34698,plain,
    ( r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top
    | k1_tarski(sK11) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34159,c_68,c_62,c_200,c_201,c_2767,c_2850])).

cnf(c_34699,plain,
    ( k1_tarski(sK11) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top ),
    inference(renaming,[status(thm)],[c_34698])).

cnf(c_35,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2190,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34704,plain,
    ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13
    | k1_tarski(sK11) = k1_xboole_0
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_34699,c_2190])).

cnf(c_84237,plain,
    ( k1_tarski(sK11) = k1_xboole_0
    | k7_relat_1(sK13,k1_tarski(sK11)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34704,c_68,c_2767])).

cnf(c_84238,plain,
    ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13
    | k1_tarski(sK11) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_84237])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f174])).

cnf(c_2201,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2921,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2201])).

cnf(c_33,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2192,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6717,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_2921,c_2192])).

cnf(c_21,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_32,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6722,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6717,c_21,c_32])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2205,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6737,plain,
    ( k1_tarski(X0) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6722,c_2205])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2214,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7611,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2214])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2216,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4515,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2216])).

cnf(c_7636,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7611,c_4515])).

cnf(c_63762,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6737,c_7636])).

cnf(c_84241,plain,
    ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_84238,c_63762])).

cnf(c_2170,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_5384,plain,
    ( v1_relat_1(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_2170])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2198,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5754,plain,
    ( k2_relat_1(k7_relat_1(sK13,X0)) = k9_relat_1(sK13,X0) ),
    inference(superposition,[status(thm)],[c_5384,c_2198])).

cnf(c_84257,plain,
    ( k9_relat_1(sK13,k1_tarski(sK11)) = k2_relat_1(sK13) ),
    inference(superposition,[status(thm)],[c_84241,c_5754])).

cnf(c_54,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k1_tarski(X1))),k1_tarski(k1_funct_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_2172,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k1_tarski(X1))),k1_tarski(k1_funct_1(X0,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_7423,plain,
    ( r1_tarski(k9_relat_1(sK13,k1_tarski(X0)),k1_tarski(k1_funct_1(sK13,X0))) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_5754,c_2172])).

cnf(c_66,plain,
    ( v1_funct_1(sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_8365,plain,
    ( r1_tarski(k9_relat_1(sK13,k1_tarski(X0)),k1_tarski(k1_funct_1(sK13,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7423,c_66,c_68,c_2767])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2206,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8835,plain,
    ( k9_relat_1(sK13,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK13,X0))
    | k9_relat_1(sK13,k1_tarski(X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8365,c_2206])).

cnf(c_84561,plain,
    ( k9_relat_1(sK13,k1_tarski(sK11)) = k1_xboole_0
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relat_1(sK13) ),
    inference(superposition,[status(thm)],[c_84257,c_8835])).

cnf(c_84574,plain,
    ( k2_relat_1(sK13) = k1_xboole_0
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relat_1(sK13) ),
    inference(demodulation,[status(thm)],[c_84561,c_84257])).

cnf(c_1022,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_11060,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1025,c_1022])).

cnf(c_81011,plain,
    ( r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
    | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X0) ),
    inference(resolution,[status(thm)],[c_80636,c_11060])).

cnf(c_31,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_11040,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_1025,c_31])).

cnf(c_33895,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11040,c_1022])).

cnf(c_7637,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7636])).

cnf(c_34915,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33895,c_7637])).

cnf(c_83662,plain,
    ( ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_81011,c_34915])).

cnf(c_6916,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1023,c_1022])).

cnf(c_80992,plain,
    ( sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) ),
    inference(resolution,[status(thm)],[c_80636,c_6916])).

cnf(c_83004,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | ~ r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X1)
    | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X0) ),
    inference(resolution,[status(thm)],[c_80992,c_11014])).

cnf(c_83006,plain,
    ( ~ r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),k1_xboole_0)
    | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_83004])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | sK1(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_61970,plain,
    ( ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
    | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_funct_1(sK13,sK11)
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2871,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_5885,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X2))
    | X1 != X0
    | k1_tarski(X2) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_59512,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
    | X1 != X0
    | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_5885])).

cnf(c_59514,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
    | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_tarski(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_59512])).

cnf(c_9212,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK13)
    | k2_relat_1(sK13) != X1 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_9213,plain,
    ( k2_relat_1(sK13) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK13)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9212])).

cnf(c_1026,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_5342,plain,
    ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != X0
    | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_5345,plain,
    ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k1_xboole_0
    | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5342])).

cnf(c_3558,plain,
    ( X0 != X1
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) != X1
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_5085,plain,
    ( X0 != k2_relat_1(sK13)
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_3558])).

cnf(c_5086,plain,
    ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13)
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_5085])).

cnf(c_2847,plain,
    ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != X0
    | k1_tarski(k1_funct_1(sK13,sK11)) != X0
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_3563,plain,
    ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13)
    | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13)
    | k1_tarski(k1_funct_1(sK13,sK11)) != k2_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_2847])).

cnf(c_57,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_2851,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
    | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k2_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_206,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88561,c_84574,c_83662,c_83006,c_80073,c_61970,c_59514,c_9213,c_5345,c_5086,c_3563,c_2851,c_206,c_201,c_200,c_61,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.40/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.40/4.50  
% 31.40/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.40/4.50  
% 31.40/4.50  ------  iProver source info
% 31.40/4.50  
% 31.40/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.40/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.40/4.50  git: non_committed_changes: false
% 31.40/4.50  git: last_make_outside_of_git: false
% 31.40/4.50  
% 31.40/4.50  ------ 
% 31.40/4.50  ------ Parsing...
% 31.40/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.40/4.50  
% 31.40/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 31.40/4.50  
% 31.40/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.40/4.50  
% 31.40/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.40/4.50  ------ Proving...
% 31.40/4.50  ------ Problem Properties 
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  clauses                                 65
% 31.40/4.50  conjectures                             5
% 31.40/4.50  EPR                                     2
% 31.40/4.50  Horn                                    52
% 31.40/4.50  unary                                   15
% 31.40/4.50  binary                                  17
% 31.40/4.50  lits                                    187
% 31.40/4.50  lits eq                                 53
% 31.40/4.50  fd_pure                                 0
% 31.40/4.50  fd_pseudo                               0
% 31.40/4.50  fd_cond                                 2
% 31.40/4.50  fd_pseudo_cond                          11
% 31.40/4.50  AC symbols                              0
% 31.40/4.50  
% 31.40/4.50  ------ Input Options Time Limit: Unbounded
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  ------ 
% 31.40/4.50  Current options:
% 31.40/4.50  ------ 
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  ------ Proving...
% 31.40/4.50  
% 31.40/4.50  
% 31.40/4.50  % SZS status Theorem for theBenchmark.p
% 31.40/4.50  
% 31.40/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.40/4.50  
% 31.40/4.50  fof(f4,axiom,(
% 31.40/4.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f75,plain,(
% 31.40/4.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 31.40/4.50    inference(nnf_transformation,[],[f4])).
% 31.40/4.50  
% 31.40/4.50  fof(f76,plain,(
% 31.40/4.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.40/4.50    inference(rectify,[],[f75])).
% 31.40/4.50  
% 31.40/4.50  fof(f77,plain,(
% 31.40/4.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 31.40/4.50    introduced(choice_axiom,[])).
% 31.40/4.50  
% 31.40/4.50  fof(f78,plain,(
% 31.40/4.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.40/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f76,f77])).
% 31.40/4.50  
% 31.40/4.50  fof(f110,plain,(
% 31.40/4.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 31.40/4.50    inference(cnf_transformation,[],[f78])).
% 31.40/4.50  
% 31.40/4.50  fof(f173,plain,(
% 31.40/4.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 31.40/4.50    inference(equality_resolution,[],[f110])).
% 31.40/4.50  
% 31.40/4.50  fof(f112,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f78])).
% 31.40/4.50  
% 31.40/4.50  fof(f33,conjecture,(
% 31.40/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f34,negated_conjecture,(
% 31.40/4.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 31.40/4.50    inference(negated_conjecture,[],[f33])).
% 31.40/4.50  
% 31.40/4.50  fof(f70,plain,(
% 31.40/4.50    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 31.40/4.50    inference(ennf_transformation,[],[f34])).
% 31.40/4.50  
% 31.40/4.50  fof(f71,plain,(
% 31.40/4.50    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 31.40/4.50    inference(flattening,[],[f70])).
% 31.40/4.50  
% 31.40/4.50  fof(f103,plain,(
% 31.40/4.50    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13) & k1_xboole_0 != sK12 & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) & v1_funct_2(sK13,k1_tarski(sK11),sK12) & v1_funct_1(sK13))),
% 31.40/4.50    introduced(choice_axiom,[])).
% 31.40/4.50  
% 31.40/4.50  fof(f104,plain,(
% 31.40/4.50    k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13) & k1_xboole_0 != sK12 & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) & v1_funct_2(sK13,k1_tarski(sK11),sK12) & v1_funct_1(sK13)),
% 31.40/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f71,f103])).
% 31.40/4.50  
% 31.40/4.50  fof(f170,plain,(
% 31.40/4.50    k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13)),
% 31.40/4.50    inference(cnf_transformation,[],[f104])).
% 31.40/4.50  
% 31.40/4.50  fof(f166,plain,(
% 31.40/4.50    v1_funct_1(sK13)),
% 31.40/4.50    inference(cnf_transformation,[],[f104])).
% 31.40/4.50  
% 31.40/4.50  fof(f167,plain,(
% 31.40/4.50    v1_funct_2(sK13,k1_tarski(sK11),sK12)),
% 31.40/4.50    inference(cnf_transformation,[],[f104])).
% 31.40/4.50  
% 31.40/4.50  fof(f168,plain,(
% 31.40/4.50    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))),
% 31.40/4.50    inference(cnf_transformation,[],[f104])).
% 31.40/4.50  
% 31.40/4.50  fof(f169,plain,(
% 31.40/4.50    k1_xboole_0 != sK12),
% 31.40/4.50    inference(cnf_transformation,[],[f104])).
% 31.40/4.50  
% 31.40/4.50  fof(f32,axiom,(
% 31.40/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f68,plain,(
% 31.40/4.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.40/4.50    inference(ennf_transformation,[],[f32])).
% 31.40/4.50  
% 31.40/4.50  fof(f69,plain,(
% 31.40/4.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.40/4.50    inference(flattening,[],[f68])).
% 31.40/4.50  
% 31.40/4.50  fof(f165,plain,(
% 31.40/4.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f69])).
% 31.40/4.50  
% 31.40/4.50  fof(f111,plain,(
% 31.40/4.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 31.40/4.50    inference(cnf_transformation,[],[f78])).
% 31.40/4.50  
% 31.40/4.50  fof(f171,plain,(
% 31.40/4.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 31.40/4.50    inference(equality_resolution,[],[f111])).
% 31.40/4.50  
% 31.40/4.50  fof(f172,plain,(
% 31.40/4.50    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 31.40/4.50    inference(equality_resolution,[],[f171])).
% 31.40/4.50  
% 31.40/4.50  fof(f31,axiom,(
% 31.40/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f66,plain,(
% 31.40/4.50    ! [X0,X1,X2,X3] : ((? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.40/4.50    inference(ennf_transformation,[],[f31])).
% 31.40/4.50  
% 31.40/4.50  fof(f67,plain,(
% 31.40/4.50    ! [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.40/4.50    inference(flattening,[],[f66])).
% 31.40/4.50  
% 31.40/4.50  fof(f101,plain,(
% 31.40/4.50    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) => (k1_funct_1(X3,sK10(X0,X2,X3)) = X2 & r2_hidden(sK10(X0,X2,X3),X0)))),
% 31.40/4.50    introduced(choice_axiom,[])).
% 31.40/4.50  
% 31.40/4.50  fof(f102,plain,(
% 31.40/4.50    ! [X0,X1,X2,X3] : ((k1_funct_1(X3,sK10(X0,X2,X3)) = X2 & r2_hidden(sK10(X0,X2,X3),X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.40/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f67,f101])).
% 31.40/4.50  
% 31.40/4.50  fof(f164,plain,(
% 31.40/4.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X3,sK10(X0,X2,X3)) = X2 | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f102])).
% 31.40/4.50  
% 31.40/4.50  fof(f8,axiom,(
% 31.40/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f83,plain,(
% 31.40/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.40/4.50    inference(nnf_transformation,[],[f8])).
% 31.40/4.50  
% 31.40/4.50  fof(f121,plain,(
% 31.40/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f83])).
% 31.40/4.50  
% 31.40/4.50  fof(f17,axiom,(
% 31.40/4.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f45,plain,(
% 31.40/4.50    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 31.40/4.50    inference(ennf_transformation,[],[f17])).
% 31.40/4.50  
% 31.40/4.50  fof(f131,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 31.40/4.50    inference(cnf_transformation,[],[f45])).
% 31.40/4.50  
% 31.40/4.50  fof(f19,axiom,(
% 31.40/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f48,plain,(
% 31.40/4.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.40/4.50    inference(ennf_transformation,[],[f19])).
% 31.40/4.50  
% 31.40/4.50  fof(f49,plain,(
% 31.40/4.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.40/4.50    inference(flattening,[],[f48])).
% 31.40/4.50  
% 31.40/4.50  fof(f134,plain,(
% 31.40/4.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f49])).
% 31.40/4.50  
% 31.40/4.50  fof(f10,axiom,(
% 31.40/4.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f124,plain,(
% 31.40/4.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f10])).
% 31.40/4.50  
% 31.40/4.50  fof(f5,axiom,(
% 31.40/4.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f79,plain,(
% 31.40/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.40/4.50    inference(nnf_transformation,[],[f5])).
% 31.40/4.50  
% 31.40/4.50  fof(f80,plain,(
% 31.40/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.40/4.50    inference(flattening,[],[f79])).
% 31.40/4.50  
% 31.40/4.50  fof(f114,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f80])).
% 31.40/4.50  
% 31.40/4.50  fof(f115,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.40/4.50    inference(cnf_transformation,[],[f80])).
% 31.40/4.50  
% 31.40/4.50  fof(f175,plain,(
% 31.40/4.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.40/4.50    inference(equality_resolution,[],[f115])).
% 31.40/4.50  
% 31.40/4.50  fof(f29,axiom,(
% 31.40/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f64,plain,(
% 31.40/4.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.40/4.50    inference(ennf_transformation,[],[f29])).
% 31.40/4.50  
% 31.40/4.50  fof(f161,plain,(
% 31.40/4.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f64])).
% 31.40/4.50  
% 31.40/4.50  fof(f23,axiom,(
% 31.40/4.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f52,plain,(
% 31.40/4.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.40/4.50    inference(ennf_transformation,[],[f23])).
% 31.40/4.50  
% 31.40/4.50  fof(f53,plain,(
% 31.40/4.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 31.40/4.50    inference(flattening,[],[f52])).
% 31.40/4.50  
% 31.40/4.50  fof(f140,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f53])).
% 31.40/4.50  
% 31.40/4.50  fof(f116,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.40/4.50    inference(cnf_transformation,[],[f80])).
% 31.40/4.50  
% 31.40/4.50  fof(f174,plain,(
% 31.40/4.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.40/4.50    inference(equality_resolution,[],[f116])).
% 31.40/4.50  
% 31.40/4.50  fof(f21,axiom,(
% 31.40/4.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f50,plain,(
% 31.40/4.50    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 31.40/4.50    inference(ennf_transformation,[],[f21])).
% 31.40/4.50  
% 31.40/4.50  fof(f138,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f50])).
% 31.40/4.50  
% 31.40/4.50  fof(f12,axiom,(
% 31.40/4.50    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f126,plain,(
% 31.40/4.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f12])).
% 31.40/4.50  
% 31.40/4.50  fof(f20,axiom,(
% 31.40/4.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f136,plain,(
% 31.40/4.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.40/4.50    inference(cnf_transformation,[],[f20])).
% 31.40/4.50  
% 31.40/4.50  fof(f7,axiom,(
% 31.40/4.50    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f37,plain,(
% 31.40/4.50    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 31.40/4.50    inference(ennf_transformation,[],[f7])).
% 31.40/4.50  
% 31.40/4.50  fof(f120,plain,(
% 31.40/4.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f37])).
% 31.40/4.50  
% 31.40/4.50  fof(f3,axiom,(
% 31.40/4.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f109,plain,(
% 31.40/4.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 31.40/4.50    inference(cnf_transformation,[],[f3])).
% 31.40/4.50  
% 31.40/4.50  fof(f2,axiom,(
% 31.40/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f35,plain,(
% 31.40/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.40/4.50    inference(rectify,[],[f2])).
% 31.40/4.50  
% 31.40/4.50  fof(f36,plain,(
% 31.40/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.40/4.50    inference(ennf_transformation,[],[f35])).
% 31.40/4.50  
% 31.40/4.50  fof(f73,plain,(
% 31.40/4.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 31.40/4.50    introduced(choice_axiom,[])).
% 31.40/4.50  
% 31.40/4.50  fof(f74,plain,(
% 31.40/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.40/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f73])).
% 31.40/4.50  
% 31.40/4.50  fof(f108,plain,(
% 31.40/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f74])).
% 31.40/4.50  
% 31.40/4.50  fof(f1,axiom,(
% 31.40/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f72,plain,(
% 31.40/4.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.40/4.50    inference(nnf_transformation,[],[f1])).
% 31.40/4.50  
% 31.40/4.50  fof(f106,plain,(
% 31.40/4.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.40/4.50    inference(cnf_transformation,[],[f72])).
% 31.40/4.50  
% 31.40/4.50  fof(f14,axiom,(
% 31.40/4.50    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f41,plain,(
% 31.40/4.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 31.40/4.50    inference(ennf_transformation,[],[f14])).
% 31.40/4.50  
% 31.40/4.50  fof(f128,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f41])).
% 31.40/4.50  
% 31.40/4.50  fof(f27,axiom,(
% 31.40/4.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f60,plain,(
% 31.40/4.50    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 31.40/4.50    inference(ennf_transformation,[],[f27])).
% 31.40/4.50  
% 31.40/4.50  fof(f61,plain,(
% 31.40/4.50    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 31.40/4.50    inference(flattening,[],[f60])).
% 31.40/4.50  
% 31.40/4.50  fof(f159,plain,(
% 31.40/4.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f61])).
% 31.40/4.50  
% 31.40/4.50  fof(f6,axiom,(
% 31.40/4.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f81,plain,(
% 31.40/4.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 31.40/4.50    inference(nnf_transformation,[],[f6])).
% 31.40/4.50  
% 31.40/4.50  fof(f82,plain,(
% 31.40/4.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 31.40/4.50    inference(flattening,[],[f81])).
% 31.40/4.50  
% 31.40/4.50  fof(f117,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f82])).
% 31.40/4.50  
% 31.40/4.50  fof(f137,plain,(
% 31.40/4.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 31.40/4.50    inference(cnf_transformation,[],[f20])).
% 31.40/4.50  
% 31.40/4.50  fof(f113,plain,(
% 31.40/4.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 31.40/4.50    inference(cnf_transformation,[],[f78])).
% 31.40/4.50  
% 31.40/4.50  fof(f30,axiom,(
% 31.40/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.40/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.40/4.50  
% 31.40/4.50  fof(f65,plain,(
% 31.40/4.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.40/4.50    inference(ennf_transformation,[],[f30])).
% 31.40/4.50  
% 31.40/4.50  fof(f162,plain,(
% 31.40/4.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.40/4.50    inference(cnf_transformation,[],[f65])).
% 31.40/4.50  
% 31.40/4.50  cnf(c_1025,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.40/4.50      theory(equality) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_8,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 31.40/4.50      inference(cnf_transformation,[],[f173]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_11014,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,X1)
% 31.40/4.50      | r2_hidden(X2,X3)
% 31.40/4.50      | ~ r2_hidden(X3,k1_tarski(X1))
% 31.40/4.50      | X2 != X0 ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_1025,c_8]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_6,plain,
% 31.40/4.50      ( r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0 | k1_tarski(X0) = X1 ),
% 31.40/4.50      inference(cnf_transformation,[],[f112]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_1032,plain,
% 31.40/4.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 31.40/4.50      theory(equality) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_9129,plain,
% 31.40/4.50      ( r2_hidden(sK1(X0,X1),X1)
% 31.40/4.50      | ~ v1_relat_1(X0)
% 31.40/4.50      | v1_relat_1(sK1(X0,X1))
% 31.40/4.50      | k1_tarski(X0) = X1 ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_6,c_1032]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_61,negated_conjecture,
% 31.40/4.50      ( k1_tarski(k1_funct_1(sK13,sK11)) != k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.50      inference(cnf_transformation,[],[f170]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_79076,plain,
% 31.40/4.50      ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | ~ v1_relat_1(k1_funct_1(sK13,sK11))
% 31.40/4.50      | v1_relat_1(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_9129,c_61]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_65,negated_conjecture,
% 31.40/4.50      ( v1_funct_1(sK13) ),
% 31.40/4.50      inference(cnf_transformation,[],[f166]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_64,negated_conjecture,
% 31.40/4.50      ( v1_funct_2(sK13,k1_tarski(sK11),sK12) ),
% 31.40/4.50      inference(cnf_transformation,[],[f167]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_63,negated_conjecture,
% 31.40/4.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) ),
% 31.40/4.50      inference(cnf_transformation,[],[f168]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_62,negated_conjecture,
% 31.40/4.50      ( k1_xboole_0 != sK12 ),
% 31.40/4.50      inference(cnf_transformation,[],[f169]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2868,plain,
% 31.40/4.50      ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
% 31.40/4.50      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_60,plain,
% 31.40/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.40/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.40/4.50      | ~ r2_hidden(X3,X1)
% 31.40/4.50      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 31.40/4.50      | ~ v1_funct_1(X0)
% 31.40/4.50      | k1_xboole_0 = X2 ),
% 31.40/4.50      inference(cnf_transformation,[],[f165]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2955,plain,
% 31.40/4.50      ( ~ v1_funct_2(sK13,X0,X1)
% 31.40/4.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.40/4.50      | ~ r2_hidden(X2,X0)
% 31.40/4.50      | r2_hidden(k1_funct_1(sK13,X2),k2_relset_1(X0,X1,sK13))
% 31.40/4.50      | ~ v1_funct_1(sK13)
% 31.40/4.50      | k1_xboole_0 = X1 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_60]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_3237,plain,
% 31.40/4.50      ( ~ v1_funct_2(sK13,k1_tarski(X0),X1)
% 31.40/4.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
% 31.40/4.50      | ~ r2_hidden(X0,k1_tarski(X0))
% 31.40/4.50      | r2_hidden(k1_funct_1(sK13,X0),k2_relset_1(k1_tarski(X0),X1,sK13))
% 31.40/4.50      | ~ v1_funct_1(sK13)
% 31.40/4.50      | k1_xboole_0 = X1 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_2955]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4204,plain,
% 31.40/4.50      ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
% 31.40/4.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
% 31.40/4.50      | r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | ~ r2_hidden(sK11,k1_tarski(sK11))
% 31.40/4.50      | ~ v1_funct_1(sK13)
% 31.40/4.50      | k1_xboole_0 = sK12 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_3237]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_7,plain,
% 31.40/4.50      ( r2_hidden(X0,k1_tarski(X0)) ),
% 31.40/4.50      inference(cnf_transformation,[],[f172]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4821,plain,
% 31.40/4.50      ( r2_hidden(sK11,k1_tarski(sK11)) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_7]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_3552,plain,
% 31.40/4.50      ( ~ r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(X0))
% 31.40/4.50      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_8]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4953,plain,
% 31.40/4.50      ( ~ r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
% 31.40/4.50      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_3552]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4954,plain,
% 31.40/4.50      ( r2_hidden(k2_relset_1(k1_tarski(sK11),sK12,sK13),k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13))) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_7]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4431,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,X1)
% 31.40/4.50      | r2_hidden(sK1(X2,X3),X3)
% 31.40/4.50      | X3 != X1
% 31.40/4.50      | sK1(X2,X3) != X0 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_1025]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_8630,plain,
% 31.40/4.50      ( ~ r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | r2_hidden(sK1(X0,X1),X1)
% 31.40/4.50      | X1 != k2_relset_1(k1_tarski(sK11),sK12,sK13)
% 31.40/4.50      | sK1(X0,X1) != k1_funct_1(sK13,sK11) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_4431]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_23126,plain,
% 31.40/4.50      ( ~ r2_hidden(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relset_1(k1_tarski(sK11),sK12,sK13)
% 31.40/4.50      | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_funct_1(sK13,sK11) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_8630]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_80073,plain,
% 31.40/4.50      ( r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_79076,c_65,c_64,c_63,c_62,c_61,c_2868,c_4204,c_4821,
% 31.40/4.50                 c_4953,c_4954,c_23126]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_58,plain,
% 31.40/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.40/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.40/4.50      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 31.40/4.50      | ~ v1_funct_1(X0)
% 31.40/4.50      | k1_funct_1(X0,sK10(X1,X3,X0)) = X3 ),
% 31.40/4.50      inference(cnf_transformation,[],[f164]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_80086,plain,
% 31.40/4.50      ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
% 31.40/4.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
% 31.40/4.50      | ~ v1_funct_1(sK13)
% 31.40/4.50      | k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_80073,c_58]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_62021,plain,
% 31.40/4.50      ( ~ v1_funct_2(sK13,k1_tarski(sK11),sK12)
% 31.40/4.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
% 31.40/4.50      | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.50      | ~ v1_funct_1(sK13)
% 31.40/4.50      | k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_58]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_80636,plain,
% 31.40/4.50      ( k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) = sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_80086,c_65,c_64,c_63,c_62,c_61,c_2868,c_4204,c_4821,
% 31.40/4.50                 c_4953,c_4954,c_23126,c_62021]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_82978,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_tarski(X1))
% 31.40/4.50      | r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
% 31.40/4.50      | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X1) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_11014,c_80636]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_88551,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
% 31.40/4.50      | r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
% 31.40/4.50      | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
% 31.40/4.50      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_82978,c_6]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_88561,plain,
% 31.40/4.50      ( r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),k1_xboole_0)
% 31.40/4.50      | ~ r2_hidden(k1_xboole_0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
% 31.40/4.50      | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK11)
% 31.40/4.50      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_88551]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2165,plain,
% 31.40/4.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_17,plain,
% 31.40/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.40/4.50      inference(cnf_transformation,[],[f121]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2203,plain,
% 31.40/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.40/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_5572,plain,
% 31.40/4.50      ( r1_tarski(sK13,k2_zfmisc_1(k1_tarski(sK11),sK12)) = iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_2165,c_2203]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_27,plain,
% 31.40/4.50      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | k1_xboole_0 = X0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f131]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_30,plain,
% 31.40/4.50      ( ~ r1_tarski(X0,X1)
% 31.40/4.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 31.40/4.50      | ~ v1_relat_1(X0)
% 31.40/4.50      | ~ v1_relat_1(X1) ),
% 31.40/4.50      inference(cnf_transformation,[],[f134]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2193,plain,
% 31.40/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.40/4.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 31.40/4.50      | v1_relat_1(X0) != iProver_top
% 31.40/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_14516,plain,
% 31.40/4.50      ( k1_xboole_0 = X0
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 31.40/4.50      | r1_tarski(k1_relat_1(X2),X0) = iProver_top
% 31.40/4.50      | v1_relat_1(X2) != iProver_top
% 31.40/4.50      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_27,c_2193]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_19,plain,
% 31.40/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.40/4.50      inference(cnf_transformation,[],[f124]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_176,plain,
% 31.40/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34150,plain,
% 31.40/4.50      ( v1_relat_1(X2) != iProver_top
% 31.40/4.50      | r1_tarski(k1_relat_1(X2),X0) = iProver_top
% 31.40/4.50      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | k1_xboole_0 = X0 ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_14516,c_176]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34151,plain,
% 31.40/4.50      ( k1_xboole_0 = X0
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | r1_tarski(X2,k2_zfmisc_1(X1,X0)) != iProver_top
% 31.40/4.50      | r1_tarski(k1_relat_1(X2),X1) = iProver_top
% 31.40/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.40/4.50      inference(renaming,[status(thm)],[c_34150]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34159,plain,
% 31.40/4.50      ( k1_tarski(sK11) = k1_xboole_0
% 31.40/4.50      | sK12 = k1_xboole_0
% 31.40/4.50      | r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top
% 31.40/4.50      | v1_relat_1(sK13) != iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_5572,c_34151]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_68,plain,
% 31.40/4.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_11,plain,
% 31.40/4.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | k1_xboole_0 = X0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f114]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_200,plain,
% 31.40/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.40/4.50      | k1_xboole_0 = k1_xboole_0 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_11]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_10,plain,
% 31.40/4.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f175]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_201,plain,
% 31.40/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_10]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_56,plain,
% 31.40/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.40/4.50      | v1_relat_1(X0) ),
% 31.40/4.50      inference(cnf_transformation,[],[f161]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2766,plain,
% 31.40/4.50      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
% 31.40/4.50      | v1_relat_1(sK13) ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_56]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2767,plain,
% 31.40/4.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12))) != iProver_top
% 31.40/4.50      | v1_relat_1(sK13) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_2766]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_1023,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2849,plain,
% 31.40/4.50      ( sK12 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK12 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_1023]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2850,plain,
% 31.40/4.50      ( sK12 != k1_xboole_0
% 31.40/4.50      | k1_xboole_0 = sK12
% 31.40/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.40/4.50      inference(instantiation,[status(thm)],[c_2849]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34698,plain,
% 31.40/4.50      ( r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top
% 31.40/4.50      | k1_tarski(sK11) = k1_xboole_0 ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_34159,c_68,c_62,c_200,c_201,c_2767,c_2850]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34699,plain,
% 31.40/4.50      ( k1_tarski(sK11) = k1_xboole_0
% 31.40/4.50      | r1_tarski(k1_relat_1(sK13),k1_tarski(sK11)) = iProver_top ),
% 31.40/4.50      inference(renaming,[status(thm)],[c_34698]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_35,plain,
% 31.40/4.50      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 31.40/4.50      | ~ v1_relat_1(X0)
% 31.40/4.50      | k7_relat_1(X0,X1) = X0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f140]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2190,plain,
% 31.40/4.50      ( k7_relat_1(X0,X1) = X0
% 31.40/4.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.40/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34704,plain,
% 31.40/4.50      ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13
% 31.40/4.50      | k1_tarski(sK11) = k1_xboole_0
% 31.40/4.50      | v1_relat_1(sK13) != iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_34699,c_2190]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84237,plain,
% 31.40/4.50      ( k1_tarski(sK11) = k1_xboole_0
% 31.40/4.50      | k7_relat_1(sK13,k1_tarski(sK11)) = sK13 ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_34704,c_68,c_2767]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84238,plain,
% 31.40/4.50      ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13
% 31.40/4.50      | k1_tarski(sK11) = k1_xboole_0 ),
% 31.40/4.50      inference(renaming,[status(thm)],[c_84237]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_9,plain,
% 31.40/4.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f174]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2201,plain,
% 31.40/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2921,plain,
% 31.40/4.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_9,c_2201]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_33,plain,
% 31.40/4.50      ( ~ v1_relat_1(X0)
% 31.40/4.50      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 31.40/4.50      inference(cnf_transformation,[],[f138]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2192,plain,
% 31.40/4.50      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 31.40/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_6717,plain,
% 31.40/4.50      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_2921,c_2192]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_21,plain,
% 31.40/4.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f126]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_32,plain,
% 31.40/4.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f136]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_6722,plain,
% 31.40/4.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.40/4.50      inference(light_normalisation,[status(thm)],[c_6717,c_21,c_32]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_15,plain,
% 31.40/4.50      ( r2_hidden(X0,X1)
% 31.40/4.50      | k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0) ),
% 31.40/4.50      inference(cnf_transformation,[],[f120]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2205,plain,
% 31.40/4.50      ( k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)
% 31.40/4.50      | r2_hidden(X1,X0) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_6737,plain,
% 31.40/4.50      ( k1_tarski(X0) != k1_xboole_0
% 31.40/4.50      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_6722,c_2205]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4,plain,
% 31.40/4.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f109]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 31.40/4.50      inference(cnf_transformation,[],[f108]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2214,plain,
% 31.40/4.50      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 31.40/4.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_7611,plain,
% 31.40/4.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 31.40/4.50      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_4,c_2214]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_0,plain,
% 31.40/4.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f106]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2216,plain,
% 31.40/4.50      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 31.40/4.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_4515,plain,
% 31.40/4.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_4,c_2216]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_7636,plain,
% 31.40/4.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 31.40/4.50      inference(forward_subsumption_resolution,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_7611,c_4515]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_63762,plain,
% 31.40/4.50      ( k1_tarski(X0) != k1_xboole_0 ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_6737,c_7636]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84241,plain,
% 31.40/4.50      ( k7_relat_1(sK13,k1_tarski(sK11)) = sK13 ),
% 31.40/4.50      inference(forward_subsumption_resolution,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_84238,c_63762]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2170,plain,
% 31.40/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.40/4.50      | v1_relat_1(X0) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_5384,plain,
% 31.40/4.50      ( v1_relat_1(sK13) = iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_2165,c_2170]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_23,plain,
% 31.40/4.50      ( ~ v1_relat_1(X0)
% 31.40/4.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 31.40/4.50      inference(cnf_transformation,[],[f128]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2198,plain,
% 31.40/4.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 31.40/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_5754,plain,
% 31.40/4.50      ( k2_relat_1(k7_relat_1(sK13,X0)) = k9_relat_1(sK13,X0) ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_5384,c_2198]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84257,plain,
% 31.40/4.50      ( k9_relat_1(sK13,k1_tarski(sK11)) = k2_relat_1(sK13) ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_84241,c_5754]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_54,plain,
% 31.40/4.50      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k1_tarski(X1))),k1_tarski(k1_funct_1(X0,X1)))
% 31.40/4.50      | ~ v1_funct_1(X0)
% 31.40/4.50      | ~ v1_relat_1(X0) ),
% 31.40/4.50      inference(cnf_transformation,[],[f159]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2172,plain,
% 31.40/4.50      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k1_tarski(X1))),k1_tarski(k1_funct_1(X0,X1))) = iProver_top
% 31.40/4.50      | v1_funct_1(X0) != iProver_top
% 31.40/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_7423,plain,
% 31.40/4.50      ( r1_tarski(k9_relat_1(sK13,k1_tarski(X0)),k1_tarski(k1_funct_1(sK13,X0))) = iProver_top
% 31.40/4.50      | v1_funct_1(sK13) != iProver_top
% 31.40/4.50      | v1_relat_1(sK13) != iProver_top ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_5754,c_2172]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_66,plain,
% 31.40/4.50      ( v1_funct_1(sK13) = iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_8365,plain,
% 31.40/4.50      ( r1_tarski(k9_relat_1(sK13,k1_tarski(X0)),k1_tarski(k1_funct_1(sK13,X0))) = iProver_top ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_7423,c_66,c_68,c_2767]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_14,plain,
% 31.40/4.50      ( ~ r1_tarski(X0,k1_tarski(X1))
% 31.40/4.50      | k1_tarski(X1) = X0
% 31.40/4.50      | k1_xboole_0 = X0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f117]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_2206,plain,
% 31.40/4.50      ( k1_tarski(X0) = X1
% 31.40/4.50      | k1_xboole_0 = X1
% 31.40/4.50      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 31.40/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_8835,plain,
% 31.40/4.50      ( k9_relat_1(sK13,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK13,X0))
% 31.40/4.50      | k9_relat_1(sK13,k1_tarski(X0)) = k1_xboole_0 ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_8365,c_2206]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84561,plain,
% 31.40/4.50      ( k9_relat_1(sK13,k1_tarski(sK11)) = k1_xboole_0
% 31.40/4.50      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relat_1(sK13) ),
% 31.40/4.50      inference(superposition,[status(thm)],[c_84257,c_8835]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_84574,plain,
% 31.40/4.50      ( k2_relat_1(sK13) = k1_xboole_0
% 31.40/4.50      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relat_1(sK13) ),
% 31.40/4.50      inference(demodulation,[status(thm)],[c_84561,c_84257]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_1022,plain,( X0 = X0 ),theory(equality) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_11060,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_1025,c_1022]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_81011,plain,
% 31.40/4.50      ( r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X0)
% 31.40/4.50      | ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X0) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_80636,c_11060]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_31,plain,
% 31.40/4.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.40/4.50      inference(cnf_transformation,[],[f137]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_11040,plain,
% 31.40/4.50      ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
% 31.40/4.50      | ~ r2_hidden(X1,k1_xboole_0)
% 31.40/4.50      | X0 != X1 ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_1025,c_31]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_33895,plain,
% 31.40/4.50      ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
% 31.40/4.50      | ~ r2_hidden(X0,k1_xboole_0) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_11040,c_1022]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_7637,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 31.40/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_7636]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_34915,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 31.40/4.50      inference(global_propositional_subsumption,
% 31.40/4.50                [status(thm)],
% 31.40/4.50                [c_33895,c_7637]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_83662,plain,
% 31.40/4.50      ( ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k1_xboole_0) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_81011,c_34915]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_6916,plain,
% 31.40/4.50      ( X0 != X1 | X1 = X0 ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_1023,c_1022]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_80992,plain,
% 31.40/4.50      ( sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_80636,c_6916]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_83004,plain,
% 31.40/4.50      ( ~ r2_hidden(X0,k1_tarski(X1))
% 31.40/4.50      | ~ r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),X1)
% 31.40/4.50      | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),X0) ),
% 31.40/4.50      inference(resolution,[status(thm)],[c_80992,c_11014]) ).
% 31.40/4.50  
% 31.40/4.50  cnf(c_83006,plain,
% 31.40/4.50      ( ~ r2_hidden(k1_funct_1(sK13,sK10(k1_tarski(sK11),sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),sK13)),k1_xboole_0)
% 31.40/4.51      | r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k1_xboole_0)
% 31.40/4.51      | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_83004]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5,plain,
% 31.40/4.51      ( ~ r2_hidden(sK1(X0,X1),X1)
% 31.40/4.51      | sK1(X0,X1) != X0
% 31.40/4.51      | k1_tarski(X0) = X1 ),
% 31.40/4.51      inference(cnf_transformation,[],[f113]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_61970,plain,
% 31.40/4.51      ( ~ r2_hidden(sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)),k2_relset_1(k1_tarski(sK11),sK12,sK13))
% 31.40/4.51      | sK1(k1_funct_1(sK13,sK11),k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_funct_1(sK13,sK11)
% 31.40/4.51      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_5]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_2871,plain,
% 31.40/4.51      ( r2_hidden(X0,X1)
% 31.40/4.51      | ~ r2_hidden(X2,k1_tarski(X2))
% 31.40/4.51      | X0 != X2
% 31.40/4.51      | X1 != k1_tarski(X2) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_1025]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5885,plain,
% 31.40/4.51      ( ~ r2_hidden(X0,k1_tarski(X0))
% 31.40/4.51      | r2_hidden(X1,k1_tarski(X2))
% 31.40/4.51      | X1 != X0
% 31.40/4.51      | k1_tarski(X2) != k1_tarski(X0) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_2871]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_59512,plain,
% 31.40/4.51      ( ~ r2_hidden(X0,k1_tarski(X0))
% 31.40/4.51      | r2_hidden(X1,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
% 31.40/4.51      | X1 != X0
% 31.40/4.51      | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_tarski(X0) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_5885]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_59514,plain,
% 31.40/4.51      ( r2_hidden(k1_xboole_0,k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)))
% 31.40/4.51      | ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 31.40/4.51      | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) != k1_tarski(k1_xboole_0)
% 31.40/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_59512]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_9212,plain,
% 31.40/4.51      ( X0 != X1 | X0 = k2_relat_1(sK13) | k2_relat_1(sK13) != X1 ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_1023]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_9213,plain,
% 31.40/4.51      ( k2_relat_1(sK13) != k1_xboole_0
% 31.40/4.51      | k1_xboole_0 = k2_relat_1(sK13)
% 31.40/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_9212]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_1026,plain,
% 31.40/4.51      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 31.40/4.51      theory(equality) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5342,plain,
% 31.40/4.51      ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != X0
% 31.40/4.51      | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_tarski(X0) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5345,plain,
% 31.40/4.51      ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k1_xboole_0
% 31.40/4.51      | k1_tarski(k2_relset_1(k1_tarski(sK11),sK12,sK13)) = k1_tarski(k1_xboole_0) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_5342]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_3558,plain,
% 31.40/4.51      ( X0 != X1
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) != X1
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0 ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_1023]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5085,plain,
% 31.40/4.51      ( X0 != k2_relat_1(sK13)
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = X0
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_3558]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_5086,plain,
% 31.40/4.51      ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13)
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k1_xboole_0
% 31.40/4.51      | k1_xboole_0 != k2_relat_1(sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_5085]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_2847,plain,
% 31.40/4.51      ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != X0
% 31.40/4.51      | k1_tarski(k1_funct_1(sK13,sK11)) != X0
% 31.40/4.51      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_1023]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_3563,plain,
% 31.40/4.51      ( k2_relset_1(k1_tarski(sK11),sK12,sK13) != k2_relat_1(sK13)
% 31.40/4.51      | k1_tarski(k1_funct_1(sK13,sK11)) = k2_relset_1(k1_tarski(sK11),sK12,sK13)
% 31.40/4.51      | k1_tarski(k1_funct_1(sK13,sK11)) != k2_relat_1(sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_2847]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_57,plain,
% 31.40/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.40/4.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.40/4.51      inference(cnf_transformation,[],[f162]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_2851,plain,
% 31.40/4.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK11),sK12)))
% 31.40/4.51      | k2_relset_1(k1_tarski(sK11),sK12,sK13) = k2_relat_1(sK13) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_57]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(c_206,plain,
% 31.40/4.51      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 31.40/4.51      inference(instantiation,[status(thm)],[c_7]) ).
% 31.40/4.51  
% 31.40/4.51  cnf(contradiction,plain,
% 31.40/4.51      ( $false ),
% 31.40/4.51      inference(minisat,
% 31.40/4.51                [status(thm)],
% 31.40/4.51                [c_88561,c_84574,c_83662,c_83006,c_80073,c_61970,c_59514,
% 31.40/4.51                 c_9213,c_5345,c_5086,c_3563,c_2851,c_206,c_201,c_200,
% 31.40/4.51                 c_61,c_63]) ).
% 31.40/4.51  
% 31.40/4.51  
% 31.40/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.40/4.51  
% 31.40/4.51  ------                               Statistics
% 31.40/4.51  
% 31.40/4.51  ------ Selected
% 31.40/4.51  
% 31.40/4.51  total_time:                             3.516
% 31.40/4.51  
%------------------------------------------------------------------------------
