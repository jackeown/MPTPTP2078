%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0877+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 47.76s
% Output     : CNFRefutation 47.76s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 223 expanded)
%              Number of clauses        :   40 (  58 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 ( 612 expanded)
%              Number of equality atoms :  184 ( 526 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1323,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1324,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f1323])).

fof(f2676,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1324])).

fof(f2677,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f2676])).

fof(f3692,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK381 != sK384
        | sK380 != sK383
        | sK379 != sK382 )
      & k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
      & k3_zfmisc_1(sK379,sK380,sK381) = k3_zfmisc_1(sK382,sK383,sK384) ) ),
    introduced(choice_axiom,[])).

fof(f3693,plain,
    ( ( sK381 != sK384
      | sK380 != sK383
      | sK379 != sK382 )
    & k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381)
    & k3_zfmisc_1(sK379,sK380,sK381) = k3_zfmisc_1(sK382,sK383,sK384) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK379,sK380,sK381,sK382,sK383,sK384])],[f2677,f3692])).

fof(f6021,plain,(
    k3_zfmisc_1(sK379,sK380,sK381) = k3_zfmisc_1(sK382,sK383,sK384) ),
    inference(cnf_transformation,[],[f3693])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5901,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6775,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381) = k2_zfmisc_1(k2_zfmisc_1(sK382,sK383),sK384) ),
    inference(definition_unfolding,[],[f6021,f5901,f5901])).

fof(f1322,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2674,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1322])).

fof(f2675,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f2674])).

fof(f6018,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2675])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3711,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6773,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6018,f3711,f3711,f3711,f5901,f5901])).

fof(f6019,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2675])).

fof(f6772,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6019,f3711,f3711,f3711,f5901,f5901])).

fof(f6020,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2675])).

fof(f6771,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6020,f3711,f3711,f3711,f5901,f5901])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1474,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f4097,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1474])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1440,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f3886,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1440])).

fof(f6164,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f3886,f3711])).

fof(f6022,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK379,sK380,sK381) ),
    inference(cnf_transformation,[],[f3693])).

fof(f6774,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381) ),
    inference(definition_unfolding,[],[f6022,f3711,f5901])).

fof(f296,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1473,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f4096,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1473])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4462,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4399,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f6049,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f4399,f3711])).

fof(f6467,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f4462,f6049])).

fof(f6023,plain,
    ( sK381 != sK384
    | sK380 != sK383
    | sK379 != sK382 ),
    inference(cnf_transformation,[],[f3693])).

cnf(c_32620,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_161192,plain,
    ( sK379 = sK379 ),
    inference(instantiation,[status(thm)],[c_32620])).

cnf(c_32621,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_125266,plain,
    ( sK382 != X0
    | sK379 != X0
    | sK379 = sK382 ),
    inference(instantiation,[status(thm)],[c_32621])).

cnf(c_161191,plain,
    ( sK382 != sK379
    | sK379 = sK382
    | sK379 != sK379 ),
    inference(instantiation,[status(thm)],[c_125266])).

cnf(c_32627,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_159429,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK379)
    | sK379 != X0 ),
    inference(instantiation,[status(thm)],[c_32627])).

cnf(c_159434,plain,
    ( v1_xboole_0(sK379)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK379 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_159429])).

cnf(c_157274,plain,
    ( sK380 = sK380 ),
    inference(instantiation,[status(thm)],[c_32620])).

cnf(c_104970,plain,
    ( sK383 != X0
    | sK380 != X0
    | sK380 = sK383 ),
    inference(instantiation,[status(thm)],[c_32621])).

cnf(c_157273,plain,
    ( sK383 != sK380
    | sK380 = sK383
    | sK380 != sK380 ),
    inference(instantiation,[status(thm)],[c_104970])).

cnf(c_153279,plain,
    ( sK381 = sK381 ),
    inference(instantiation,[status(thm)],[c_32620])).

cnf(c_87011,plain,
    ( sK384 != X0
    | sK381 != X0
    | sK381 = sK384 ),
    inference(instantiation,[status(thm)],[c_32621])).

cnf(c_153278,plain,
    ( sK384 != sK381
    | sK381 = sK384
    | sK381 != sK381 ),
    inference(instantiation,[status(thm)],[c_87011])).

cnf(c_149388,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK380)
    | sK380 != X0 ),
    inference(instantiation,[status(thm)],[c_32627])).

cnf(c_149393,plain,
    ( v1_xboole_0(sK380)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK380 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_149388])).

cnf(c_138867,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK381)
    | sK381 != X0 ),
    inference(instantiation,[status(thm)],[c_32627])).

cnf(c_138872,plain,
    ( v1_xboole_0(sK381)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK381 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_138867])).

cnf(c_2301,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381) = k2_zfmisc_1(k2_zfmisc_1(sK382,sK383),sK384) ),
    inference(cnf_transformation,[],[f6775])).

cnf(c_2298,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f6773])).

cnf(c_113667,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | sK382 = X0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_2301,c_2298])).

cnf(c_114829,plain,
    ( sK382 = sK379
    | sK379 = o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK381 = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_113667])).

cnf(c_2297,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f6772])).

cnf(c_110142,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | sK383 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_2301,c_2297])).

cnf(c_111021,plain,
    ( sK379 = o_0_0_xboole_0
    | sK383 = sK380
    | sK380 = o_0_0_xboole_0
    | sK381 = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_110142])).

cnf(c_2296,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f6771])).

cnf(c_109859,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)
    | sK384 = X2
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_2301,c_2296])).

cnf(c_110650,plain,
    ( sK379 = o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0
    | sK384 = sK381
    | sK381 = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_109859])).

cnf(c_381,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4097])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f6164])).

cnf(c_2300,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381) ),
    inference(cnf_transformation,[],[f6774])).

cnf(c_85582,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK379,sK380),sK381)) ),
    inference(resolution,[status(thm)],[c_181,c_2300])).

cnf(c_85629,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK379,sK380)) ),
    inference(resolution,[status(thm)],[c_381,c_85582])).

cnf(c_380,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f4096])).

cnf(c_85637,plain,
    ( ~ v1_xboole_0(sK380) ),
    inference(resolution,[status(thm)],[c_85629,c_380])).

cnf(c_85635,plain,
    ( ~ v1_xboole_0(sK379) ),
    inference(resolution,[status(thm)],[c_85629,c_381])).

cnf(c_85609,plain,
    ( ~ v1_xboole_0(sK381) ),
    inference(resolution,[status(thm)],[c_85582,c_380])).

cnf(c_745,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6467])).

cnf(c_2299,negated_conjecture,
    ( sK379 != sK382
    | sK380 != sK383
    | sK381 != sK384 ),
    inference(cnf_transformation,[],[f6023])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_161192,c_161191,c_159434,c_157274,c_157273,c_153279,c_153278,c_149393,c_138872,c_114829,c_111021,c_110650,c_85637,c_85635,c_85609,c_745,c_2299])).

%------------------------------------------------------------------------------
