%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UxKLZH1VNX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  328 ( 527 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C_2 @ X0 )
      | ( r2_hidden @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_2 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['22','32'])).

thf('34',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(clc,[status(thm)],['12','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UxKLZH1VNX
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 97 iterations in 0.039s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(t50_subset_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.49               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.49                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.49                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.49                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.21/0.49  thf('0', plain, (~ (r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d5_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.21/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d2_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X26 @ X27)
% 0.21/0.49          | (r2_hidden @ X26 @ X27)
% 0.21/0.49          | (v1_xboole_0 @ X27))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf('6', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(d5_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.49          | (r2_hidden @ X7 @ X9)
% 0.21/0.49          | (r2_hidden @ X7 @ X10)
% 0.21/0.49          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.49          | (r2_hidden @ X7 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_A)
% 0.21/0.49          | (r2_hidden @ sk_C_2 @ X0)
% 0.21/0.49          | (r2_hidden @ sk_C_2 @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r2_hidden @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.21/0.49        | (r2_hidden @ sk_C_2 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '9'])).
% 0.21/0.49  thf('11', plain, (~ (r2_hidden @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_2 @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i]:
% 0.21/0.49         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X13 : $i, X15 : $i]:
% 0.21/0.49         (((X13) = (X15))
% 0.21/0.49          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.49          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.49  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('25', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X16 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X9)
% 0.21/0.49          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X11 @ X9)
% 0.21/0.49          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.49  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('condensation', [status(thm)], ['30'])).
% 0.21/0.49  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '31'])).
% 0.21/0.49  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('simplify_reflect+', [status(thm)], ['22', '32'])).
% 0.21/0.49  thf('34', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.21/0.49      inference('clc', [status(thm)], ['12', '33'])).
% 0.21/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
