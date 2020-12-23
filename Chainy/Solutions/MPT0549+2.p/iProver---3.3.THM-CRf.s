%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0549+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 51.00s
% Output     : CNFRefutation 51.00s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_55650)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1504,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f1505,plain,(
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
    inference(rectify,[],[f1504])).

fof(f1506,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK26(X0,X1) != X0
          | ~ r2_hidden(sK26(X0,X1),X1) )
        & ( sK26(X0,X1) = X0
          | r2_hidden(sK26(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1507,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK26(X0,X1) != X0
            | ~ r2_hidden(sK26(X0,X1),X1) )
          & ( sK26(X0,X1) = X0
            | r2_hidden(sK26(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26])],[f1505,f1506])).

fof(f2111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f3693,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2111])).

fof(f3694,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f3693])).

fof(f732,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f733,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f732])).

fof(f1338,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f1859,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1338])).

fof(f1860,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1859])).

fof(f1861,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
        | k1_xboole_0 != k9_relat_1(sK156,sK155) )
      & ( r1_xboole_0(k1_relat_1(sK156),sK155)
        | k1_xboole_0 = k9_relat_1(sK156,sK155) )
      & v1_relat_1(sK156) ) ),
    introduced(choice_axiom,[])).

fof(f1862,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
      | k1_xboole_0 != k9_relat_1(sK156,sK155) )
    & ( r1_xboole_0(k1_relat_1(sK156),sK155)
      | k1_xboole_0 = k9_relat_1(sK156,sK155) )
    & v1_relat_1(sK156) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155,sK156])],[f1860,f1861])).

fof(f3027,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155)
    | k1_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f1862])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1886,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3642,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155)
    | o_0_0_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(definition_unfolding,[],[f3027,f1886])).

fof(f637,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1236,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k1_setfam_1(X1),X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f637])).

fof(f1237,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k1_setfam_1(X1),X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1236])).

fof(f2882,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_setfam_1(X1),X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1237])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1779,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2844,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1779])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1183,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2828,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f3597,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2828,f1886,f1886])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2827,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3596,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2827,f1886])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2704,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f3563,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f2704,f1886])).

fof(f128,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2052,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f128])).

fof(f3236,plain,(
    ! [X0] : ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2052,f1886])).

fof(f122,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f879,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f122])).

fof(f880,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f879])).

fof(f2046,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f880])).

fof(f3028,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | k1_xboole_0 != k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f1862])).

fof(f3641,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | o_0_0_xboole_0 != k9_relat_1(sK156,sK155) ),
    inference(definition_unfolding,[],[f3028,f1886])).

fof(f127,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f884,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f127])).

fof(f2051,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f884])).

fof(f3235,plain,(
    ! [X0] :
      ( r2_xboole_0(o_0_0_xboole_0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2051,f1886,f1886])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1497,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f2020,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1497])).

fof(f3211,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f2020,f1886])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2011,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2034,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3206,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f2011,f2034,f1886,f1886])).

fof(f3026,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1862])).

fof(f797,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1416,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f797])).

fof(f1878,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1416])).

fof(f3111,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1878])).

fof(f3670,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | o_0_0_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3111,f1886])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1484,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1484])).

fof(f1947,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1485])).

fof(f3112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1878])).

fof(f3669,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3112,f1886])).

fof(f728,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1335,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f728])).

fof(f3022,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1335])).

fof(f738,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1346,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f3034,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1346])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1586,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f1587,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1586])).

fof(f2341,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1587])).

fof(f3401,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f2341,f1886,f1886])).

fof(f3740,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f3401])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1253,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f2941,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1253])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2012,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f3207,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2012,f1886])).

fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f840,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f1976,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f840])).

fof(f586,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2821,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f586])).

fof(f769,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3071,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f769])).

fof(f3656,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3071,f1886,f1886])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3694])).

cnf(c_33918,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_1134,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK156),sK155)
    | o_0_0_xboole_0 = k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f3642])).

cnf(c_33328,plain,
    ( o_0_0_xboole_0 = k9_relat_1(sK156,sK155)
    | r1_xboole_0(k1_relat_1(sK156),sK155) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_989,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f2882])).

cnf(c_33460,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k1_setfam_1(X2),X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_188467,plain,
    ( k9_relat_1(sK156,sK155) = o_0_0_xboole_0
    | r1_xboole_0(k1_setfam_1(X0),sK155) = iProver_top
    | r2_hidden(k1_relat_1(sK156),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_33328,c_33460])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2844])).

cnf(c_1909,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_935,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3597])).

cnf(c_1945,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_934,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3596])).

cnf(c_1948,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_811,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3563])).

cnf(c_2243,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_172,plain,
    ( ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3236])).

cnf(c_3406,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_16596,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_120167,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK156,sK155),o_0_0_xboole_0)
    | k9_relat_1(sK156,sK155) != X0
    | o_0_0_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_16596])).

cnf(c_120169,plain,
    ( r1_tarski(k9_relat_1(sK156,sK155),o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | k9_relat_1(sK156,sK155) != o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_120167])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X2,X0)
    | r2_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f2046])).

cnf(c_1133,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | o_0_0_xboole_0 != k9_relat_1(sK156,sK155) ),
    inference(cnf_transformation,[],[f3641])).

cnf(c_171,plain,
    ( r2_xboole_0(o_0_0_xboole_0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3235])).

cnf(c_49733,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | r2_xboole_0(o_0_0_xboole_0,k9_relat_1(sK156,sK155)) ),
    inference(resolution,[status(thm)],[c_1133,c_171])).

cnf(c_132204,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | ~ r1_tarski(k9_relat_1(sK156,sK155),X0)
    | r2_xboole_0(o_0_0_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_166,c_49733])).

cnf(c_142,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3211])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3206])).

cnf(c_48674,plain,
    ( r1_tarski(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(resolution,[status(thm)],[c_142,c_132])).

cnf(c_132843,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | r2_xboole_0(o_0_0_xboole_0,k4_xboole_0(k9_relat_1(sK156,sK155),o_0_0_xboole_0)) ),
    inference(resolution,[status(thm)],[c_132204,c_48674])).

cnf(c_136641,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK156),sK155)
    | ~ r1_tarski(k4_xboole_0(k9_relat_1(sK156,sK155),o_0_0_xboole_0),X0)
    | r2_xboole_0(o_0_0_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_132843,c_166])).

cnf(c_1135,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f3026])).

cnf(c_1224,plain,
    ( v1_relat_1(sK156) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_1219,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3670])).

cnf(c_42875,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155)
    | ~ v1_relat_1(sK156)
    | k7_relat_1(sK156,sK155) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1947])).

cnf(c_72594,plain,
    ( ~ r1_tarski(k7_relat_1(sK156,sK155),o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,k7_relat_1(sK156,sK155))
    | k7_relat_1(sK156,sK155) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_72607,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | r1_tarski(k7_relat_1(sK156,sK155),o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k7_relat_1(sK156,sK155)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72594])).

cnf(c_1218,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3669])).

cnf(c_33265,plain,
    ( k7_relat_1(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_50258,plain,
    ( k9_relat_1(sK156,sK155) = o_0_0_xboole_0
    | k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | v1_relat_1(sK156) != iProver_top ),
    inference(superposition,[status(thm)],[c_33328,c_33265])).

cnf(c_50441,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | k9_relat_1(sK156,sK155) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_50258,c_1224])).

cnf(c_50442,plain,
    ( k9_relat_1(sK156,sK155) = o_0_0_xboole_0
    | k7_relat_1(sK156,sK155) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_50441])).

cnf(c_33327,plain,
    ( v1_relat_1(sK156) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_1129,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f3022])).

cnf(c_33332,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_128202,plain,
    ( k2_relat_1(k7_relat_1(sK156,X0)) = k9_relat_1(sK156,X0) ),
    inference(superposition,[status(thm)],[c_33327,c_33332])).

cnf(c_1141,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3034])).

cnf(c_33323,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_129122,plain,
    ( r1_tarski(k7_relat_1(sK156,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK156,X0)),k9_relat_1(sK156,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK156,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_128202,c_33323])).

cnf(c_129436,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | r1_tarski(k7_relat_1(sK156,sK155),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK156,sK155)),o_0_0_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK156,sK155)) != iProver_top ),
    inference(superposition,[status(thm)],[c_50442,c_129122])).

cnf(c_448,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3740])).

cnf(c_129462,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | r1_tarski(k7_relat_1(sK156,sK155),o_0_0_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK156,sK155)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_129436,c_448])).

cnf(c_1048,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2941])).

cnf(c_172840,plain,
    ( v1_relat_1(k7_relat_1(sK156,sK155))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_172841,plain,
    ( v1_relat_1(k7_relat_1(sK156,sK155)) = iProver_top
    | v1_relat_1(sK156) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172840])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3207])).

cnf(c_174904,plain,
    ( r1_tarski(o_0_0_xboole_0,k7_relat_1(sK156,sK155)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_174905,plain,
    ( r1_tarski(o_0_0_xboole_0,k7_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174904])).

cnf(c_175373,plain,
    ( ~ r1_tarski(k4_xboole_0(k9_relat_1(sK156,sK155),o_0_0_xboole_0),X0)
    | r2_xboole_0(o_0_0_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_136641,c_1135,c_1224,c_42875,c_72607,c_129462,c_172841,c_174905])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f1976])).

cnf(c_175397,plain,
    ( ~ r1_tarski(k9_relat_1(sK156,sK155),X0)
    | r2_xboole_0(o_0_0_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_175373,c_97])).

cnf(c_175399,plain,
    ( ~ r1_tarski(k9_relat_1(sK156,sK155),o_0_0_xboole_0)
    | r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_175397])).

cnf(c_188823,plain,
    ( r1_xboole_0(k1_setfam_1(X0),sK155) = iProver_top
    | r2_hidden(k1_relat_1(sK156),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_188467,c_1135,c_1224,c_1133,c_1945,c_1948,c_42875,c_55650,c_72607,c_129462,c_172841,c_174905])).

cnf(c_188831,plain,
    ( r1_xboole_0(k1_setfam_1(k1_tarski(k1_relat_1(sK156))),sK155) = iProver_top ),
    inference(superposition,[status(thm)],[c_33918,c_188823])).

cnf(c_928,plain,
    ( k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f2821])).

cnf(c_188848,plain,
    ( r1_xboole_0(k1_relat_1(sK156),sK155) = iProver_top ),
    inference(demodulation,[status(thm)],[c_188831,c_928])).

cnf(c_33329,plain,
    ( o_0_0_xboole_0 != k9_relat_1(sK156,sK155)
    | r1_xboole_0(k1_relat_1(sK156),sK155) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_50445,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(sK156),sK155) != iProver_top ),
    inference(superposition,[status(thm)],[c_50442,c_33329])).

cnf(c_189025,plain,
    ( k7_relat_1(sK156,sK155) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_188848,c_50445])).

cnf(c_189048,plain,
    ( k9_relat_1(sK156,sK155) = k2_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_189025,c_128202])).

cnf(c_1177,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3656])).

cnf(c_189050,plain,
    ( k9_relat_1(sK156,sK155) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_189048,c_1177])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_189050,c_175399,c_120169,c_3406,c_2243,c_1948,c_1945,c_1909])).

%------------------------------------------------------------------------------
