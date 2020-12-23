%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PILRgP08tO

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:36 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  477 ( 596 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('4',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('22',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ ( k2_xboole_0 @ X13 @ X15 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X13 ) @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X2 )
      | ( r1_tarski @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PILRgP08tO
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.01  % Solved by: fo/fo7.sh
% 0.82/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.01  % done 1495 iterations in 0.557s
% 0.82/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.01  % SZS output start Refutation
% 0.82/1.01  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.82/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.01  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.82/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.01  thf(t33_wellord2, conjecture,
% 0.82/1.01    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.82/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.01    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.82/1.01  thf('0', plain,
% 0.82/1.01      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf(d10_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.82/1.01  thf('1', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.01  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.82/1.01      inference('simplify', [status(thm)], ['1'])).
% 0.82/1.01  thf(d1_wellord2, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( v1_relat_1 @ B ) =>
% 0.82/1.01       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.82/1.01         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.82/1.01           ( ![C:$i,D:$i]:
% 0.82/1.01             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.82/1.01               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.82/1.01                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.82/1.01  thf('3', plain,
% 0.82/1.01      (![X19 : $i, X20 : $i]:
% 0.82/1.01         (((X20) != (k1_wellord2 @ X19))
% 0.82/1.01          | ((k3_relat_1 @ X20) = (X19))
% 0.82/1.01          | ~ (v1_relat_1 @ X20))),
% 0.82/1.01      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.82/1.01  thf('4', plain,
% 0.82/1.01      (![X19 : $i]:
% 0.82/1.01         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.82/1.01          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['3'])).
% 0.82/1.01  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.82/1.01  thf('5', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.82/1.01  thf('6', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf(d6_relat_1, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( v1_relat_1 @ A ) =>
% 0.82/1.01       ( ( k3_relat_1 @ A ) =
% 0.82/1.01         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.82/1.01  thf('7', plain,
% 0.82/1.01      (![X17 : $i]:
% 0.82/1.01         (((k3_relat_1 @ X17)
% 0.82/1.01            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.82/1.01          | ~ (v1_relat_1 @ X17))),
% 0.82/1.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.82/1.01  thf(t11_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.82/1.01  thf('8', plain,
% 0.82/1.01      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.01         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.82/1.01      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.82/1.01  thf('9', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.82/1.01          | ~ (v1_relat_1 @ X0)
% 0.82/1.01          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.82/1.01  thf('10', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.82/1.01          | (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1)
% 0.82/1.01          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['6', '9'])).
% 0.82/1.01  thf('11', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.82/1.01  thf('12', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.82/1.01          | (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.82/1.01      inference('demod', [status(thm)], ['10', '11'])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.82/1.01      inference('sup-', [status(thm)], ['2', '12'])).
% 0.82/1.01  thf(t12_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i]:
% 0.82/1.01         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.82/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0) = (X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.82/1.01  thf(t120_zfmisc_1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.82/1.01         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.82/1.01       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.82/1.01         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.01         ((k2_zfmisc_1 @ (k2_xboole_0 @ X13 @ X15) @ X14)
% 0.82/1.01           = (k2_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 0.82/1.01              (k2_zfmisc_1 @ X15 @ X14)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.82/1.01  thf(t7_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.82/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.82/1.01          (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['16', '17'])).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.82/1.01          (k2_zfmisc_1 @ X0 @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['15', '18'])).
% 0.82/1.01  thf('20', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.82/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (![X17 : $i]:
% 0.82/1.01         (((k3_relat_1 @ X17)
% 0.82/1.01            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.82/1.01          | ~ (v1_relat_1 @ X17))),
% 0.82/1.01      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.82/1.01         ((k2_zfmisc_1 @ X16 @ (k2_xboole_0 @ X13 @ X15))
% 0.82/1.01           = (k2_xboole_0 @ (k2_zfmisc_1 @ X16 @ X13) @ 
% 0.82/1.01              (k2_zfmisc_1 @ X16 @ X15)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.82/1.01  thf(t21_relat_1, axiom,
% 0.82/1.01    (![A:$i]:
% 0.82/1.01     ( ( v1_relat_1 @ A ) =>
% 0.82/1.01       ( r1_tarski @
% 0.82/1.01         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (![X18 : $i]:
% 0.82/1.01         ((r1_tarski @ X18 @ 
% 0.82/1.01           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 0.82/1.01          | ~ (v1_relat_1 @ X18))),
% 0.82/1.01      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i]:
% 0.82/1.01         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.82/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.01  thf('25', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (v1_relat_1 @ X0)
% 0.82/1.01          | ((k2_xboole_0 @ X0 @ 
% 0.82/1.01              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.82/1.01              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('26', plain,
% 0.82/1.01      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.82/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.82/1.01  thf(t10_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.82/1.01  thf('27', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.01         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.82/1.01  thf('29', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i]:
% 0.82/1.01         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.82/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.01  thf('30', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.82/1.01           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['28', '29'])).
% 0.82/1.01  thf('31', plain,
% 0.82/1.01      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.01         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.82/1.01      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.82/1.01  thf('32', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.01         (~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.82/1.01          | (r1_tarski @ X1 @ X3))),
% 0.82/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.01  thf('33', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r1_tarski @ 
% 0.82/1.01             (k2_xboole_0 @ X2 @ 
% 0.82/1.01              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))) @ 
% 0.82/1.01             X1)
% 0.82/1.01          | ~ (v1_relat_1 @ X0)
% 0.82/1.01          | (r1_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['25', '32'])).
% 0.82/1.01  thf('34', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r1_tarski @ 
% 0.82/1.01             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ 
% 0.82/1.01              (k2_xboole_0 @ X1 @ (k2_relat_1 @ X0))) @ 
% 0.82/1.01             X2)
% 0.82/1.01          | (r1_tarski @ X0 @ X2)
% 0.82/1.01          | ~ (v1_relat_1 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['22', '33'])).
% 0.82/1.01  thf('35', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ 
% 0.82/1.01             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)) @ X1)
% 0.82/1.01          | ~ (v1_relat_1 @ X0)
% 0.82/1.01          | ~ (v1_relat_1 @ X0)
% 0.82/1.01          | (r1_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['21', '34'])).
% 0.82/1.01  thf('36', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r1_tarski @ X0 @ X1)
% 0.82/1.01          | ~ (v1_relat_1 @ X0)
% 0.82/1.01          | ~ (r1_tarski @ 
% 0.82/1.01               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)) @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['35'])).
% 0.82/1.01  thf('37', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ 
% 0.82/1.01             (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0) @ X1)
% 0.82/1.01          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.82/1.01          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['20', '36'])).
% 0.82/1.01  thf('38', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.82/1.01  thf('39', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r1_tarski @ 
% 0.82/1.01             (k2_zfmisc_1 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0) @ X1)
% 0.82/1.01          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.82/1.01      inference('demod', [status(thm)], ['37', '38'])).
% 0.82/1.01  thf('40', plain,
% 0.82/1.01      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['19', '39'])).
% 0.82/1.01  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.82/1.01  
% 0.82/1.01  % SZS output end Refutation
% 0.82/1.01  
% 0.82/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
