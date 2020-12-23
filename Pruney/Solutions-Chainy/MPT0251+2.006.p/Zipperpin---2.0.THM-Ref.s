%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aA9MXQwdTf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 135 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  545 ( 831 expanded)
%              Number of equality atoms :   53 (  82 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X47 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r2_hidden @ X47 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X34 @ X33 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X28 @ X29 ) @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X25: $i] :
      ( r1_tarski @ k1_xboole_0 @ X25 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ X30 @ X31 )
        = X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','25','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','51'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aA9MXQwdTf
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:14:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 295 iterations in 0.065s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(t46_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.20/0.52  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t38_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X47 : $i, X49 : $i, X50 : $i]:
% 0.20/0.52         ((r1_tarski @ (k2_tarski @ X47 @ X49) @ X50)
% 0.20/0.52          | ~ (r2_hidden @ X49 @ X50)
% 0.20/0.52          | ~ (r2_hidden @ X47 @ X50))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.52          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('5', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X20 @ X21)
% 0.20/0.52           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(commutativity_k2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i]:
% 0.20/0.52         ((k2_tarski @ X34 @ X33) = (k2_tarski @ X33 @ X34))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf(t1_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('16', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf(t40_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k2_xboole_0 @ X28 @ X29) @ X29)
% 0.20/0.52           = (k4_xboole_0 @ X28 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('21', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.20/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X20 @ X21)
% 0.20/0.52           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('26', plain, (![X25 : $i]: (r1_tarski @ k1_xboole_0 @ X25)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X20 @ X21)
% 0.20/0.52           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf(t83_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X30 @ X31) = (X30)) | ~ (r1_xboole_0 @ X30 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X1) | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['32', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf(d4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X8)
% 0.20/0.52          | (r2_hidden @ X9 @ X7)
% 0.20/0.52          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.52         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '43'])).
% 0.20/0.52  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (sk_B @ k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '47'])).
% 0.20/0.52  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '49'])).
% 0.20/0.52  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '25', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '51'])).
% 0.20/0.52  thf(t39_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26))
% 0.20/0.52           = (k2_xboole_0 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.20/0.52         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('56', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('59', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
