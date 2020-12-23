%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tlX9FbBuvB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  375 ( 589 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t139_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X4 ) @ ( k2_zfmisc_1 @ X7 @ X6 ) )
      | ( r1_tarski @ X5 @ X7 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t139_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) @ X10 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t195_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = A )
              & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t195_relat_1])).

thf('9',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X5 ) @ ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X5 @ X7 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t139_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('21',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('28',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['10','28'])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf('31',plain,(
    v1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tlX9FbBuvB
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 47 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(t21_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( r1_tarski @
% 0.21/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         ((r1_tarski @ X14 @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.49  thf(t139_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i,C:$i,D:$i]:
% 0.21/0.49         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.21/0.49             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.21/0.49           ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_zfmisc_1 @ X5 @ X4) @ (k2_zfmisc_1 @ X7 @ X6))
% 0.21/0.49          | (r1_tarski @ X5 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t139_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.49          | (v1_xboole_0 @ X0)
% 0.21/0.49          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(fc6_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t193_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11)) @ X10)),
% 0.21/0.49      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.21/0.49          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0) | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.49  thf(t195_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.49               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.49                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))
% 0.21/0.49        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A)))
% 0.21/0.49         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         ((r1_tarski @ X14 @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X5) @ (k2_zfmisc_1 @ X6 @ X7))
% 0.21/0.49          | (r1_tarski @ X5 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t139_zfmisc_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X1)
% 0.21/0.49          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf(t194_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X12 @ X13)) @ X13)),
% 0.21/0.49      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.21/0.49          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X1) | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))
% 0.21/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((((sk_B) != (sk_B)) | (v1_xboole_0 @ sk_A)))
% 0.21/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A))
% 0.21/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.49  thf(l13_xboole_0, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))) | 
% 0.21/0.49       ~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('28', plain, (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['10', '28'])).
% 0.21/0.49  thf('30', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '29'])).
% 0.21/0.49  thf('31', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
