%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zYRTqH6upE

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:39 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  403 ( 760 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
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

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

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
    ! [X7: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X7 )
      | ( X7 = k1_xboole_0 ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zYRTqH6upE
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 273 iterations in 0.234s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.50/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.69  thf(t10_subset_1, conjecture,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.69       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.50/0.69            ( ![C:$i]:
% 0.50/0.69              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i]:
% 0.50/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.69          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.50/0.69               ( ![C:$i]:
% 0.50/0.69                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.50/0.69  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(d2_subset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.50/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.50/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.50/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      (![X22 : $i, X23 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X22 @ X23)
% 0.50/0.69          | (r2_hidden @ X22 @ X23)
% 0.50/0.69          | (v1_xboole_0 @ X23))),
% 0.50/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.69        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.69  thf(d1_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X12 @ X11)
% 0.50/0.69          | (r1_tarski @ X12 @ X10)
% 0.50/0.69          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (![X10 : $i, X12 : $i]:
% 0.50/0.69         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['3'])).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['2', '4'])).
% 0.50/0.69  thf('6', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X23 : $i, X24 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X24 @ X23)
% 0.50/0.69          | (v1_xboole_0 @ X24)
% 0.50/0.69          | ~ (v1_xboole_0 @ X23))),
% 0.50/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.69  thf('9', plain, (((r1_tarski @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '8'])).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.69         (~ (r1_tarski @ X9 @ X10)
% 0.50/0.69          | (r2_hidden @ X9 @ X11)
% 0.50/0.69          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i]:
% 0.50/0.69         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 0.50/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['9', '11'])).
% 0.50/0.69  thf(t7_xboole_0, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.50/0.69          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.69  thf(d4_tarski, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.50/0.69       ( ![C:$i]:
% 0.50/0.69         ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.69           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X14 @ X15)
% 0.50/0.69          | ~ (r2_hidden @ X16 @ X14)
% 0.50/0.69          | (r2_hidden @ X16 @ X17)
% 0.50/0.69          | ((X17) != (k3_tarski @ X15)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d4_tarski])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.69         ((r2_hidden @ X16 @ (k3_tarski @ X15))
% 0.50/0.69          | ~ (r2_hidden @ X16 @ X14)
% 0.50/0.69          | ~ (r2_hidden @ X14 @ X15))),
% 0.50/0.69      inference('simplify', [status(thm)], ['14'])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         (((X0) = (k1_xboole_0))
% 0.50/0.69          | ~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['13', '15'])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.69        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))
% 0.50/0.69        | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['12', '16'])).
% 0.50/0.69  thf(t99_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.50/0.69  thf('18', plain, (![X21 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X21)) = (X21))),
% 0.50/0.69      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.69        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.50/0.69        | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.69  thf('20', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('21', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.50/0.69  thf('22', plain,
% 0.50/0.69      (![X22 : $i, X23 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X22 @ X23)
% 0.50/0.69          | (m1_subset_1 @ X22 @ X23)
% 0.50/0.69          | (v1_xboole_0 @ X23))),
% 0.50/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.69  thf('23', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.69        | (v1_xboole_0 @ sk_A)
% 0.50/0.69        | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.69  thf('25', plain,
% 0.50/0.69      (![X25 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X25 @ sk_B_1) | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      ((((sk_B_1) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.69  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('28', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.50/0.69  thf('29', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.69      inference('clc', [status(thm)], ['23', '28'])).
% 0.50/0.69  thf(t6_boole, axiom,
% 0.50/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.50/0.69      inference('cnf', [status(esa)], [t6_boole])).
% 0.50/0.69  thf('31', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.69  thf('32', plain, (((r1_tarski @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '8'])).
% 0.50/0.69  thf('33', plain,
% 0.50/0.69      (((r1_tarski @ sk_B_1 @ k1_xboole_0)
% 0.50/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.50/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.50/0.69  thf('34', plain,
% 0.50/0.69      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ sk_B_1 @ k1_xboole_0))),
% 0.50/0.69      inference('simplify', [status(thm)], ['33'])).
% 0.50/0.69  thf(t61_xboole_1, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.50/0.69  thf('35', plain,
% 0.50/0.69      (![X7 : $i]: ((r2_xboole_0 @ k1_xboole_0 @ X7) | ((X7) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.50/0.69  thf(d8_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.50/0.69       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.50/0.69  thf('36', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.50/0.69  thf('37', plain,
% 0.50/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.69  thf(d10_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.69  thf('38', plain,
% 0.50/0.69      (![X4 : $i, X6 : $i]:
% 0.50/0.69         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.50/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.69  thf('39', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (((X0) = (k1_xboole_0))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.50/0.69          | ((X0) = (k1_xboole_0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.69  thf('40', plain,
% 0.50/0.69      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['39'])).
% 0.50/0.69  thf('41', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['34', '40'])).
% 0.50/0.69  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('43', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.50/0.69  thf('44', plain,
% 0.50/0.69      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.50/0.69      inference('cnf', [status(esa)], [t6_boole])).
% 0.50/0.69  thf('45', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.69  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('47', plain, ($false),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
