%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QtI6JE255f

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 247 expanded)
%              Number of leaves         :   16 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  321 (2028 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(t22_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r1_tarski @ A @ B )
                    & ( r2_hidden @ B @ C ) )
                 => ( r2_hidden @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( v1_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('7',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('9',plain,
    ( ~ ( v1_ordinal1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['17'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('20',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_xboole_0 @ X12 @ X11 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('22',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( v3_ordinal1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_A = sk_C_1 ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A = sk_C_1 ),
    inference(clc,[status(thm)],['25','26'])).

thf('31',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_xboole_0 @ X12 @ X11 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('36',plain,
    ( ( sk_A = sk_B_1 )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('41',plain,(
    sk_A = sk_C_1 ),
    inference(clc,[status(thm)],['25','26'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('45',plain,(
    sk_A = sk_B_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['31','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['28','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QtI6JE255f
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 86 iterations in 0.050s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.19/0.50  thf(t22_ordinal1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( v3_ordinal1 @ C ) =>
% 0.19/0.50               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.19/0.50                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( v1_ordinal1 @ A ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( v3_ordinal1 @ B ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( v3_ordinal1 @ C ) =>
% 0.19/0.50                  ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.19/0.50                    ( r2_hidden @ A @ C ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t22_ordinal1])).
% 0.19/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('2', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.50  thf(cc1_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.19/0.50  thf('6', plain, (![X7 : $i]: ((v1_ordinal1 @ X7) | ~ (v3_ordinal1 @ X7))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.19/0.50  thf('7', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d2_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_ordinal1 @ A ) <=>
% 0.19/0.50       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X8 @ X9)
% 0.19/0.50          | (r1_tarski @ X8 @ X9)
% 0.19/0.50          | ~ (v1_ordinal1 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.19/0.50  thf('9', plain, ((~ (v1_ordinal1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((~ (v3_ordinal1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.50  thf('11', plain, ((v3_ordinal1 @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('12', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (((r1_tarski @ sk_A @ sk_C_1) | (r1_tarski @ sk_A @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf(d8_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.19/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i]:
% 0.19/0.50         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.50  thf('20', plain, ((((sk_A) = (sk_C_1)) | (r2_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf(t21_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.19/0.50           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X11)
% 0.19/0.50          | (r2_hidden @ X12 @ X11)
% 0.19/0.50          | ~ (r2_xboole_0 @ X12 @ X11)
% 0.19/0.50          | ~ (v1_ordinal1 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      ((((sk_A) = (sk_C_1))
% 0.19/0.50        | ~ (v1_ordinal1 @ sk_A)
% 0.19/0.50        | (r2_hidden @ sk_A @ sk_C_1)
% 0.19/0.50        | ~ (v3_ordinal1 @ sk_C_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain, ((v1_ordinal1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain, ((v3_ordinal1 @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain, ((((sk_A) = (sk_C_1)) | (r2_hidden @ sk_A @ sk_C_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.50  thf('26', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '27'])).
% 0.19/0.50  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('30', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('31', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i]:
% 0.19/0.50         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.50  thf('34', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X11)
% 0.19/0.50          | (r2_hidden @ X12 @ X11)
% 0.19/0.50          | ~ (r2_xboole_0 @ X12 @ X11)
% 0.19/0.50          | ~ (v1_ordinal1 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      ((((sk_A) = (sk_B_1))
% 0.19/0.50        | ~ (v1_ordinal1 @ sk_A)
% 0.19/0.50        | (r2_hidden @ sk_A @ sk_B_1)
% 0.19/0.50        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain, ((v1_ordinal1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('38', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain, ((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf('41', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain, ((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '42'])).
% 0.19/0.50  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '27'])).
% 0.19/0.50  thf('45', plain, (((sk_A) = (sk_B_1))),
% 0.19/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '45'])).
% 0.19/0.50  thf('47', plain, ($false), inference('demod', [status(thm)], ['28', '46'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
