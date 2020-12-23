%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfvCKd3gOn

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 ( 596 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B_1 )
      | ( r2_hidden @ X18 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['14'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('17',plain,(
    ~ ( r2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_1 )
      | ( r2_hidden @ X18 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['30'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('33',plain,
    ( ( sk_C_1 = sk_B_1 )
    | ( r2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['17','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfvCKd3gOn
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 304 iterations in 0.172s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf(t8_subset_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62           ( ( ![D:$i]:
% 0.42/0.62               ( ( m1_subset_1 @ D @ A ) =>
% 0.42/0.62                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.42/0.62             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62          ( ![C:$i]:
% 0.42/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62              ( ( ![D:$i]:
% 0.42/0.62                  ( ( m1_subset_1 @ D @ A ) =>
% 0.42/0.62                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.42/0.62                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.42/0.62  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(l3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X15 @ X16)
% 0.42/0.62          | (r2_hidden @ X15 @ X17)
% 0.42/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf(d2_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.42/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.42/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X12 @ X13)
% 0.42/0.62          | (m1_subset_1 @ X12 @ X13)
% 0.42/0.62          | (v1_xboole_0 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.42/0.62  thf(d1_xboole_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.42/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_B_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X18 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X18 @ sk_B_1)
% 0.42/0.62          | (r2_hidden @ X18 @ sk_C_1)
% 0.42/0.62          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_B_1 @ X0)
% 0.42/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.42/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.42/0.62          | (r1_tarski @ sk_B_1 @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.62  thf(t60_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X11 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.42/0.62  thf('17', plain, (~ (r2_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X15 @ X16)
% 0.42/0.62          | (r2_hidden @ X15 @ X17)
% 0.42/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.42/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_C_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X18 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X18 @ sk_C_1)
% 0.42/0.62          | (r2_hidden @ X18 @ sk_B_1)
% 0.42/0.62          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_C_1 @ X0)
% 0.42/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.42/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.42/0.62          | (r1_tarski @ sk_C_1 @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (((r1_tarski @ sk_C_1 @ sk_B_1) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.62  thf(d8_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.42/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X7 : $i, X9 : $i]:
% 0.42/0.62         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.42/0.62  thf('33', plain, ((((sk_C_1) = (sk_B_1)) | (r2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('34', plain, (((sk_B_1) != (sk_C_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('35', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain, ($false), inference('demod', [status(thm)], ['17', '35'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
