%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cqRf6tSk6W

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:36 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   57 (  68 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  353 ( 446 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( ( k3_relat_1 @ X14 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X11 ) @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( ( k3_relat_1 @ X14 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cqRf6tSk6W
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 168 iterations in 0.176s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.42/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(t33_wellord2, conjecture,
% 0.42/0.61    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(d1_wellord2, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ B ) =>
% 0.42/0.61       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.42/0.61         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.42/0.61           ( ![C:$i,D:$i]:
% 0.42/0.61             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.42/0.61               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.42/0.61                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         (((X17) != (k1_wellord2 @ X16))
% 0.42/0.61          | ((k3_relat_1 @ X17) = (X16))
% 0.42/0.61          | ~ (v1_relat_1 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X16 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.42/0.61          | ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.61  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.42/0.61  thf('3', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.61  thf('4', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.42/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(d6_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( ( k3_relat_1 @ A ) =
% 0.42/0.61         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X14 : $i]:
% 0.42/0.61         (((k3_relat_1 @ X14)
% 0.42/0.61            = (k2_xboole_0 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.42/0.61          | ~ (v1_relat_1 @ X14))),
% 0.42/0.61      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.42/0.61  thf(t10_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['5', '9'])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['4', '10'])).
% 0.42/0.61  thf('12', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.42/0.61  thf(t118_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.42/0.61       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.42/0.61         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X11 @ X12)
% 0.42/0.61          | (r1_tarski @ (k2_zfmisc_1 @ X13 @ X11) @ (k2_zfmisc_1 @ X13 @ X12)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (r1_tarski @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ 
% 0.42/0.61          (k2_zfmisc_1 @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('16', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.42/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X14 : $i]:
% 0.42/0.61         (((k3_relat_1 @ X14)
% 0.42/0.61            = (k2_xboole_0 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.42/0.61          | ~ (v1_relat_1 @ X14))),
% 0.42/0.61      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.42/0.61  thf(t7_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['16', '19'])).
% 0.42/0.61  thf('21', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X11 @ X12)
% 0.42/0.61          | (r1_tarski @ (k2_zfmisc_1 @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.42/0.61          (k2_zfmisc_1 @ X0 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf(t21_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( r1_tarski @
% 0.42/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X15 : $i]:
% 0.42/0.61         ((r1_tarski @ X15 @ 
% 0.42/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.42/0.61          | ~ (v1_relat_1 @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.42/0.61  thf(t1_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.61       ( r1_tarski @ A @ C ) ))).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X6 @ X7)
% 0.42/0.61          | ~ (r1_tarski @ X7 @ X8)
% 0.42/0.61          | (r1_tarski @ X6 @ X8))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (r1_tarski @ X0 @ X1)
% 0.42/0.61          | ~ (r1_tarski @ 
% 0.42/0.61               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.42/0.61           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.42/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['24', '27'])).
% 0.42/0.61  thf('29', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.42/0.61          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.42/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X6 @ X7)
% 0.42/0.61          | ~ (r1_tarski @ X7 @ X8)
% 0.42/0.61          | (r1_tarski @ X6 @ X8))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.42/0.61          | ~ (r1_tarski @ 
% 0.42/0.61               (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '32'])).
% 0.42/0.61  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
