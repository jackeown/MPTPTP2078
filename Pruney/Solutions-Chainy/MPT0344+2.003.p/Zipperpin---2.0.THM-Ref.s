%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e5cRfwykd6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:38 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  403 ( 760 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('18',plain,(
    ! [X21: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['23','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X8 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e5cRfwykd6
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 273 iterations in 0.169s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(t10_subset_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62            ( ![C:$i]:
% 0.43/0.62              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62               ( ![C:$i]:
% 0.43/0.62                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.43/0.62  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d2_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X22 @ X23)
% 0.43/0.62          | (r2_hidden @ X22 @ X23)
% 0.43/0.62          | (v1_xboole_0 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.62        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf(d1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X12 @ X11)
% 0.43/0.62          | (r1_tarski @ X12 @ X10)
% 0.43/0.62          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X10 : $i, X12 : $i]:
% 0.43/0.62         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '4'])).
% 0.43/0.62  thf('6', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X24 @ X23)
% 0.43/0.62          | (v1_xboole_0 @ X24)
% 0.43/0.62          | ~ (v1_xboole_0 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.62  thf('9', plain, (((r1_tarski @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X9 @ X10)
% 0.43/0.62          | (r2_hidden @ X9 @ X11)
% 0.43/0.62          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 0.43/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '11'])).
% 0.43/0.62  thf(t7_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf(d4_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.62           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X14 @ X15)
% 0.43/0.62          | ~ (r2_hidden @ X16 @ X14)
% 0.43/0.62          | (r2_hidden @ X16 @ X17)
% 0.43/0.62          | ((X17) != (k3_tarski @ X15)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_tarski])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((r2_hidden @ X16 @ (k3_tarski @ X15))
% 0.43/0.62          | ~ (r2_hidden @ X16 @ X14)
% 0.43/0.62          | ~ (r2_hidden @ X14 @ X15))),
% 0.43/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((X0) = (k1_xboole_0))
% 0.43/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.43/0.62          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))
% 0.43/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '16'])).
% 0.43/0.62  thf(t99_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.43/0.62  thf('18', plain, (![X21 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X21)) = (X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.43/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X22 @ X23)
% 0.43/0.62          | (m1_subset_1 @ X22 @ X23)
% 0.43/0.62          | (v1_xboole_0 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (v1_xboole_0 @ sk_A)
% 0.43/0.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X25 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X25 @ sk_B_1) | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((((sk_B_1) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('28', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.43/0.62  thf('29', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['23', '28'])).
% 0.43/0.62  thf(l13_xboole_0, axiom,
% 0.43/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('31', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain, (((r1_tarski @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (((r1_tarski @ sk_B_1 @ k1_xboole_0)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ sk_B_1 @ k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.43/0.62  thf(t61_xboole_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X8 : $i]: ((r2_xboole_0 @ k1_xboole_0 @ X8) | ((X8) = (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.43/0.62  thf(d8_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.43/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf(d10_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i]:
% 0.43/0.62         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((X0) = (k1_xboole_0))
% 0.43/0.62          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.43/0.62          | ((X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.62  thf('41', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['34', '40'])).
% 0.43/0.62  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('43', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('45', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('47', plain, ($false),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
