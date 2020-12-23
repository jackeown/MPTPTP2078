%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WDkcsrFAlW

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 217 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :   18
%              Number of atoms          :  390 (1591 expanded)
%              Number of equality atoms :   37 ( 210 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['6','21'])).

thf('36',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['6','21'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference('sup+',[status(thm)],['23','27'])).

thf('43',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','47'])).

thf('49',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WDkcsrFAlW
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 202 iterations in 0.074s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(t44_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.20/0.53  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t7_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.53  thf('4', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X7 : $i, X9 : $i]:
% 0.20/0.53         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.53        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(l27_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X48 : $i, X49 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.20/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.53  thf('9', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('11', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf(t4_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '16'])).
% 0.20/0.53  thf('18', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf(l1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X45 : $i, X47 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.20/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.53  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '21'])).
% 0.20/0.53  thf('23', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('25', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf(t10_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.53          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('30', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('32', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_C_1) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '21'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X48 : $i, X49 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.20/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X45 : $i, X47 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.20/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ sk_B_1 @ X0) | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '21'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '27'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X7 : $i, X9 : $i]:
% 0.20/0.53         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('44', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, (((sk_B_1) != (sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.53  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '47'])).
% 0.20/0.53  thf('49', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '48'])).
% 0.20/0.53  thf('50', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
