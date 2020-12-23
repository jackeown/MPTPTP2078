%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sc90BL4l7

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  464 ( 755 expanded)
%              Number of equality atoms :   68 ( 125 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) @ X12 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
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
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) @ X15 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
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
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('30',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['10','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sc90BL4l7
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:29:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 65 iterations in 0.031s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(t21_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( r1_tarski @
% 0.20/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         ((r1_tarski @ X16 @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.49  thf(t138_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.49       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.49          | (r1_tarski @ X6 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t193_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13)) @ X12)),
% 0.20/0.49      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.49          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf(t195_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.49               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.49                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))
% 0.20/0.49        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         ((r1_tarski @ X16 @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.49          | (r1_tarski @ X7 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(t194_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X14 @ X15)) @ X15)),
% 0.20/0.49      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.49          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))
% 0.20/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((((sk_B) != (sk_B)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X4) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49         | ((sk_A) = (k1_xboole_0))
% 0.20/0.49         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.49  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))) | 
% 0.20/0.49       ~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf('30', plain, (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '31'])).
% 0.20/0.49  thf('33', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X4) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['36', '37', '38'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
