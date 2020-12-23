%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0512+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 17.93s
% Output     : CNFRefutation 17.93s
% Verified   : 
% Statistics : Number of formulae       :   55 (  86 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 132 expanded)
%              Number of equality atoms :   69 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1493,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f1494,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1493])).

fof(f2228,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1494])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1774,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3229,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f2228,f1774,f1774])).

fof(f3553,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f3229])).

fof(f685,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f686,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f685])).

fof(f1243,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f686])).

fof(f1749,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK149,k1_xboole_0)
      & v1_relat_1(sK149) ) ),
    introduced(choice_axiom,[])).

fof(f1750,plain,
    ( k1_xboole_0 != k7_relat_1(sK149,k1_xboole_0)
    & v1_relat_1(sK149) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149])],[f1243,f1749])).

fof(f2852,plain,(
    v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1750])).

fof(f753,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1324,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f753])).

fof(f2940,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1324])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1922,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3483,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f2940,f1922])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1912,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f3041,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1912,f1774])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1899,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f3033,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f1899,f1922,f1774,f1774])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2715,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3423,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2715,f1774])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1138,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2716,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1138])).

fof(f3424,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2716,f1774,f1774])).

fof(f2853,plain,(
    k1_xboole_0 != k7_relat_1(sK149,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1750])).

fof(f3452,plain,(
    o_0_0_xboole_0 != k7_relat_1(sK149,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2853,f1774,f1774])).

cnf(c_449,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3553])).

cnf(c_1072,negated_conjecture,
    ( v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f2852])).

cnf(c_48230,plain,
    ( v1_relat_1(sK149) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_1159,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f3483])).

cnf(c_48164,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_59475,plain,
    ( k4_xboole_0(sK149,k4_xboole_0(sK149,k2_zfmisc_1(X0,k2_relat_1(sK149)))) = k7_relat_1(sK149,X0) ),
    inference(superposition,[status(thm)],[c_48230,c_48164])).

cnf(c_59733,plain,
    ( k4_xboole_0(sK149,k4_xboole_0(sK149,o_0_0_xboole_0)) = k7_relat_1(sK149,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_449,c_59475])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3041])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3033])).

cnf(c_49053,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_59829,plain,
    ( k7_relat_1(sK149,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_59733,c_145,c_49053])).

cnf(c_31623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_57668,plain,
    ( k7_relat_1(sK149,o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k7_relat_1(sK149,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_31623])).

cnf(c_57669,plain,
    ( k7_relat_1(sK149,o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k7_relat_1(sK149,o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_57668])).

cnf(c_934,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3423])).

cnf(c_1743,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_935,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3424])).

cnf(c_1740,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1071,negated_conjecture,
    ( o_0_0_xboole_0 != k7_relat_1(sK149,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3452])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59829,c_57669,c_1743,c_1740,c_1071])).

%------------------------------------------------------------------------------
