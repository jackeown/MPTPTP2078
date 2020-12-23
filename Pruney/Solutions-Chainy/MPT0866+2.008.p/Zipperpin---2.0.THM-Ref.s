%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JmBmFduZPJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 289 expanded)
%              Number of leaves         :   20 (  96 expanded)
%              Depth                    :   19
%              Number of atoms          :  385 (2869 expanded)
%              Number of equality atoms :   35 ( 269 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t24_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( C
                  = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X11 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,
    ( ( ( k2_mcart_1 @ sk_C )
      = ( sk_E @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_mcart_1 @ sk_C )
      = ( sk_E @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_C )
      = ( sk_D @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( sk_D @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( sk_E @ sk_C ) )
      = sk_C ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) )
      = sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    sk_C
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('32',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('33',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JmBmFduZPJ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 43 iterations in 0.014s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.46  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(t24_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46          ( ~( ![C:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.46                 ( ( C ) =
% 0.20/0.46                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46             ( ~( ![C:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.46                    ( ( C ) =
% 0.20/0.46                      ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t24_mcart_1])).
% 0.20/0.46  thf('0', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d2_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.46       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X6 @ X7)
% 0.20/0.46          | (r2_hidden @ X6 @ X7)
% 0.20/0.46          | (v1_xboole_0 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(l139_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.46          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3))
% 0.20/0.46          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.20/0.46      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t7_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X11 : $i, X13 : $i]: ((k2_mcart_1 @ (k4_tarski @ X11 @ X13)) = (X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_C) = (sk_E @ sk_C))
% 0.20/0.46        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X8 @ X7) | (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((((k2_mcart_1 @ sk_C) = (sk_E @ sk_C)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]: ((k1_mcart_1 @ (k4_tarski @ X11 @ X12)) = (X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((((k1_mcart_1 @ sk_C) = (sk_D @ sk_C))
% 0.20/0.46        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k1_mcart_1 @ sk_C) = (sk_D @ sk_C)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((((k4_tarski @ (k1_mcart_1 @ sk_C) @ (sk_E @ sk_C)) = (sk_C))
% 0.20/0.46        | (v1_xboole_0 @ sk_C)
% 0.20/0.46        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((k4_tarski @ (sk_D @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(fc1_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((k4_tarski @ (k1_mcart_1 @ sk_C) @ (sk_E @ sk_C)) = (sk_C)))),
% 0.20/0.46      inference('clc', [status(thm)], ['17', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      ((((k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)) = (sk_C))
% 0.20/0.46        | (v1_xboole_0 @ sk_C)
% 0.20/0.46        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['10', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((sk_C) != (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('26', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf(l13_xboole_0, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('28', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf(fc10_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.20/0.46       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         ((v1_xboole_0 @ X9)
% 0.20/0.46          | (v1_xboole_0 @ X10)
% 0.20/0.46          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46        | (v1_xboole_0 @ sk_B)
% 0.20/0.46        | (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('32', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('33', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('34', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('36', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.46  thf('38', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['30', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('40', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('42', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.46  thf('43', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.46  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('46', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
