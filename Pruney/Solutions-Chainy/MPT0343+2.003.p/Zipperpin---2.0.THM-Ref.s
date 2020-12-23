%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G2uLgLxHOl

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:36 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   70 (  94 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  420 ( 721 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_C_1 )
      | ( r2_hidden @ X17 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('35',plain,(
    r1_tarski @ sk_B_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_B_1 )
      | ( r2_hidden @ X17 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['27','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G2uLgLxHOl
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 458 iterations in 0.262s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.70  thf(d3_tarski, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      (![X4 : $i, X6 : $i]:
% 0.45/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf(t8_subset_1, conjecture,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( ![C:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71           ( ( ![D:$i]:
% 0.45/0.71               ( ( m1_subset_1 @ D @ A ) =>
% 0.45/0.71                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.45/0.71             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i,B:$i]:
% 0.45/0.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71          ( ![C:$i]:
% 0.45/0.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71              ( ( ![D:$i]:
% 0.45/0.71                  ( ( m1_subset_1 @ D @ A ) =>
% 0.45/0.71                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.45/0.71                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.45/0.71  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(d2_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X13 : $i, X14 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X13 @ X14)
% 0.45/0.71          | (r2_hidden @ X13 @ X14)
% 0.45/0.71          | (v1_xboole_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.71        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.71  thf(fc1_subset_1, axiom,
% 0.45/0.71    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.71  thf('4', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.45/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.71  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('clc', [status(thm)], ['3', '4'])).
% 0.45/0.71  thf(l49_zfmisc_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.45/0.71  thf('6', plain,
% 0.45/0.71      (![X10 : $i, X11 : $i]:
% 0.45/0.71         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.45/0.71      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.45/0.71  thf('7', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf(t99_zfmisc_1, axiom,
% 0.45/0.71    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.45/0.71  thf('8', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.45/0.71      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.45/0.71  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.45/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.71          | (r2_hidden @ X3 @ X5)
% 0.45/0.71          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['0', '11'])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      (![X13 : $i, X14 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X13 @ X14)
% 0.45/0.71          | (m1_subset_1 @ X13 @ X14)
% 0.45/0.71          | (v1_xboole_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.71  thf(d1_xboole_0, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.71  thf('14', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.71  thf('15', plain,
% 0.45/0.71      (![X13 : $i, X14 : $i]:
% 0.45/0.71         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.45/0.71      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_C_1 @ X0)
% 0.45/0.71          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['12', '15'])).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X17 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X17 @ sk_C_1)
% 0.45/0.71          | (r2_hidden @ X17 @ sk_B_1)
% 0.45/0.71          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_C_1 @ X0)
% 0.45/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.45/0.71          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      (![X4 : $i, X6 : $i]:
% 0.45/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('20', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.45/0.71          | (r1_tarski @ sk_C_1 @ X0))),
% 0.45/0.71      inference('clc', [status(thm)], ['18', '19'])).
% 0.45/0.71  thf('21', plain,
% 0.45/0.71      (![X4 : $i, X6 : $i]:
% 0.45/0.71         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      (((r1_tarski @ sk_C_1 @ sk_B_1) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.71  thf('23', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.45/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.71  thf(d10_xboole_0, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.71  thf('24', plain,
% 0.45/0.71      (![X7 : $i, X9 : $i]:
% 0.45/0.71         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('25', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (sk_C_1)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.71  thf('26', plain, (((sk_B_1) != (sk_C_1))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('27', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.45/0.71      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.45/0.71  thf('28', plain,
% 0.45/0.71      (![X4 : $i, X6 : $i]:
% 0.45/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('29', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('30', plain,
% 0.45/0.71      (![X13 : $i, X14 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X13 @ X14)
% 0.45/0.71          | (r2_hidden @ X13 @ X14)
% 0.45/0.71          | (v1_xboole_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.71  thf('31', plain,
% 0.45/0.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.71        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.71  thf('32', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.45/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.71  thf('33', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('clc', [status(thm)], ['31', '32'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      (![X10 : $i, X11 : $i]:
% 0.45/0.71         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.45/0.71      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.45/0.71  thf('35', plain, ((r1_tarski @ sk_B_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.71  thf('36', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.45/0.71      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.45/0.71  thf('37', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('38', plain,
% 0.45/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.71          | (r2_hidden @ X3 @ X5)
% 0.45/0.71          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('39', plain,
% 0.45/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.71  thf('40', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['28', '39'])).
% 0.45/0.71  thf('41', plain,
% 0.45/0.71      (![X13 : $i, X14 : $i]:
% 0.45/0.71         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.45/0.71      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_B_1 @ X0)
% 0.45/0.71          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      (![X17 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X17 @ sk_B_1)
% 0.45/0.71          | (r2_hidden @ X17 @ sk_C_1)
% 0.45/0.71          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('44', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ sk_B_1 @ X0)
% 0.45/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.45/0.71          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      (![X4 : $i, X6 : $i]:
% 0.45/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('46', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.45/0.71          | (r1_tarski @ sk_B_1 @ X0))),
% 0.45/0.71      inference('clc', [status(thm)], ['44', '45'])).
% 0.45/0.71  thf('47', plain,
% 0.45/0.71      (![X4 : $i, X6 : $i]:
% 0.45/0.71         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('48', plain,
% 0.45/0.71      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.71  thf('49', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.45/0.71      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.71  thf('50', plain, ($false), inference('demod', [status(thm)], ['27', '49'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.45/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
