%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.85cYk9y0b7

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:37 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 ( 471 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( X18
       != ( k1_wellord2 @ X17 ) )
      | ( ( k3_relat_1 @ X18 )
        = X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X17 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
        = X17 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X12 ) @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.85cYk9y0b7
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:22:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 165 iterations in 0.191s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(t33_wellord2, conjecture,
% 0.47/0.65    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d1_wellord2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ B ) =>
% 0.47/0.65       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.47/0.65         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.47/0.65           ( ![C:$i,D:$i]:
% 0.47/0.65             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.47/0.65               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.47/0.65                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         (((X18) != (k1_wellord2 @ X17))
% 0.47/0.65          | ((k3_relat_1 @ X18) = (X17))
% 0.47/0.65          | ~ (v1_relat_1 @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X17 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ (k1_wellord2 @ X17))
% 0.47/0.65          | ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.65  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.47/0.65  thf('3', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.47/0.65  thf('4', plain, (![X17 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17))),
% 0.47/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf(d6_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ( k3_relat_1 @ A ) =
% 0.47/0.65         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X15 : $i]:
% 0.47/0.65         (((k3_relat_1 @ X15)
% 0.47/0.65            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.47/0.65          | ~ (v1_relat_1 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.47/0.65  thf(d3_tarski, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.65  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.65      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.65  thf(t10_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['5', '11'])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['4', '12'])).
% 0.47/0.65  thf('14', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.47/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf(t118_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) =>
% 0.47/0.65       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.47/0.65         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X12 @ X13)
% 0.47/0.65          | (r1_tarski @ (k2_zfmisc_1 @ X14 @ X12) @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (r1_tarski @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ 
% 0.47/0.65          (k2_zfmisc_1 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf('18', plain, (![X17 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17))),
% 0.47/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X15 : $i]:
% 0.47/0.65         (((k3_relat_1 @ X15)
% 0.47/0.65            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.47/0.65          | ~ (v1_relat_1 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.47/0.65  thf(t7_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.47/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['19', '20'])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['18', '21'])).
% 0.47/0.65  thf('23', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.47/0.65      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X12 @ X13)
% 0.47/0.65          | (r1_tarski @ (k2_zfmisc_1 @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.47/0.65          (k2_zfmisc_1 @ X0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf(t21_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( r1_tarski @
% 0.47/0.65         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X16 : $i]:
% 0.47/0.65         ((r1_tarski @ X16 @ 
% 0.47/0.65           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.47/0.65          | ~ (v1_relat_1 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.47/0.65  thf(t1_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.65       ( r1_tarski @ A @ C ) ))).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X7 @ X8)
% 0.47/0.65          | ~ (r1_tarski @ X8 @ X9)
% 0.47/0.65          | (r1_tarski @ X7 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (r1_tarski @ X0 @ X1)
% 0.47/0.65          | ~ (r1_tarski @ 
% 0.47/0.65               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.47/0.65           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.47/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['26', '29'])).
% 0.47/0.65  thf('31', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.47/0.65          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.47/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X7 @ X8)
% 0.47/0.65          | ~ (r1_tarski @ X8 @ X9)
% 0.47/0.65          | (r1_tarski @ X7 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.47/0.65          | ~ (r1_tarski @ 
% 0.47/0.65               (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '34'])).
% 0.47/0.65  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
