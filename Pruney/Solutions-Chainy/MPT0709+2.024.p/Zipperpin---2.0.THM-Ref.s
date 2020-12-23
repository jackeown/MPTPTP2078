%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WRFnX7UfBO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:09 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   81 (  98 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  586 ( 831 expanded)
%              Number of equality atoms :   34 (  51 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X24 ) ) @ X24 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k10_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ ( k9_relat_1 @ X29 @ X31 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t160_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('22',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( r1_tarski @ ( k10_relat_1 @ X27 @ ( k9_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WRFnX7UfBO
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 1862 iterations in 0.826s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.06/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.06/1.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.06/1.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.06/1.28  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.06/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(t78_relat_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( v1_relat_1 @ A ) =>
% 1.06/1.28       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.06/1.28  thf('0', plain,
% 1.06/1.28      (![X24 : $i]:
% 1.06/1.28         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X24)) @ X24) = (X24))
% 1.06/1.28          | ~ (v1_relat_1 @ X24))),
% 1.06/1.28      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.06/1.28  thf(t164_funct_1, conjecture,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.28       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.06/1.28         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i,B:$i]:
% 1.06/1.28        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.28          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.06/1.28            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.06/1.28  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t36_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.06/1.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.28  thf(t1_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.06/1.28       ( r1_tarski @ A @ C ) ))).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X3 @ X4)
% 1.06/1.28          | ~ (r1_tarski @ X4 @ X5)
% 1.06/1.28          | (r1_tarski @ X3 @ X5))),
% 1.06/1.28      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['1', '4'])).
% 1.06/1.28  thf(t85_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X13 @ X14)
% 1.06/1.28          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.06/1.28          (k4_xboole_0 @ X1 @ (k1_relat_1 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.28  thf(t66_xboole_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.06/1.28       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X12 @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf(t48_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X9 : $i, X10 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.06/1.28           = (k3_xboole_0 @ X9 @ X10))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.06/1.28         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['9', '10'])).
% 1.06/1.28  thf(t3_boole, axiom,
% 1.06/1.28    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.28  thf('12', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.28  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['11', '12'])).
% 1.06/1.28  thf(d10_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.06/1.28      inference('simplify', [status(thm)], ['14'])).
% 1.06/1.28  thf(t71_relat_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.06/1.28       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.06/1.28  thf('16', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.06/1.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.06/1.28  thf(t160_funct_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( v1_relat_1 @ B ) =>
% 1.06/1.28       ( ![C:$i]:
% 1.06/1.28         ( ( v1_relat_1 @ C ) =>
% 1.06/1.28           ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) ) =>
% 1.06/1.28             ( r1_tarski @
% 1.06/1.28               ( k10_relat_1 @ B @ A ) @ 
% 1.06/1.28               ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) ))).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X29)
% 1.06/1.28          | (r1_tarski @ (k10_relat_1 @ X30 @ X31) @ 
% 1.06/1.28             (k10_relat_1 @ (k5_relat_1 @ X30 @ X29) @ (k9_relat_1 @ X29 @ X31)))
% 1.06/1.28          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ (k1_relat_1 @ X29))
% 1.06/1.28          | ~ (v1_relat_1 @ X30))),
% 1.06/1.28      inference('cnf', [status(esa)], [t160_funct_1])).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.06/1.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.06/1.28          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.06/1.28             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.06/1.28              (k9_relat_1 @ X1 @ X2)))
% 1.06/1.28          | ~ (v1_relat_1 @ X1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.28  thf(fc3_funct_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.06/1.28       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.06/1.28  thf('19', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.06/1.28          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.06/1.28             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.06/1.28              (k9_relat_1 @ X1 @ X2)))
% 1.06/1.28          | ~ (v1_relat_1 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf(t43_funct_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.06/1.28       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (![X32 : $i, X33 : $i]:
% 1.06/1.28         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 1.06/1.28           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.06/1.28  thf('22', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 1.06/1.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.06/1.28  thf(t182_relat_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( v1_relat_1 @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( v1_relat_1 @ B ) =>
% 1.06/1.28           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.06/1.28             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (![X20 : $i, X21 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X20)
% 1.06/1.28          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 1.06/1.28              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 1.06/1.28          | ~ (v1_relat_1 @ X21))),
% 1.06/1.28      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.06/1.28            = (k10_relat_1 @ X1 @ X0))
% 1.06/1.28          | ~ (v1_relat_1 @ X1)
% 1.06/1.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('25', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.06/1.28            = (k10_relat_1 @ X1 @ X0))
% 1.06/1.28          | ~ (v1_relat_1 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.06/1.28            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.06/1.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['21', '26'])).
% 1.06/1.28  thf('28', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 1.06/1.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.06/1.28  thf('29', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.06/1.28          | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 1.06/1.28             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.06/1.28              (k9_relat_1 @ X1 @ X2)))
% 1.06/1.28          | ~ (v1_relat_1 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['20', '30'])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X0)
% 1.06/1.28          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.06/1.28             (k10_relat_1 @ 
% 1.06/1.28              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 1.06/1.28              (k9_relat_1 @ X0 @ X1))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['15', '31'])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (((r1_tarski @ sk_A @ 
% 1.06/1.28         (k10_relat_1 @ 
% 1.06/1.28          (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) @ 
% 1.06/1.28          (k9_relat_1 @ sk_B @ sk_A)))
% 1.06/1.28        | ~ (v1_relat_1 @ sk_B))),
% 1.06/1.28      inference('sup+', [status(thm)], ['13', '32'])).
% 1.06/1.28  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      ((r1_tarski @ sk_A @ 
% 1.06/1.28        (k10_relat_1 @ 
% 1.06/1.28         (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) @ 
% 1.06/1.28         (k9_relat_1 @ sk_B @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['33', '34'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.06/1.28        | ~ (v1_relat_1 @ sk_B))),
% 1.06/1.28      inference('sup+', [status(thm)], ['0', '35'])).
% 1.06/1.28  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('38', plain,
% 1.06/1.28      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['36', '37'])).
% 1.06/1.28  thf(t152_funct_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.28       ( ( v2_funct_1 @ B ) =>
% 1.06/1.28         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      (![X27 : $i, X28 : $i]:
% 1.06/1.28         (~ (v2_funct_1 @ X27)
% 1.06/1.28          | (r1_tarski @ (k10_relat_1 @ X27 @ (k9_relat_1 @ X27 @ X28)) @ X28)
% 1.06/1.28          | ~ (v1_funct_1 @ X27)
% 1.06/1.28          | ~ (v1_relat_1 @ X27))),
% 1.06/1.28      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      (![X0 : $i, X2 : $i]:
% 1.06/1.28         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v2_funct_1 @ X1)
% 1.06/1.28          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.06/1.28          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.28  thf('42', plain,
% 1.06/1.28      ((((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.06/1.28        | ~ (v2_funct_1 @ sk_B)
% 1.06/1.28        | ~ (v1_funct_1 @ sk_B)
% 1.06/1.28        | ~ (v1_relat_1 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['38', '41'])).
% 1.06/1.28  thf('43', plain, ((v2_funct_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('46', plain,
% 1.06/1.28      (((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 1.06/1.28  thf('47', plain,
% 1.06/1.28      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('48', plain, ($false),
% 1.06/1.28      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
