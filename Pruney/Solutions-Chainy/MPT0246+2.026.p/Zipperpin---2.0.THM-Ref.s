%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PTuGEmAJ7g

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:17 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  456 ( 729 expanded)
%              Number of equality atoms :   42 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('1',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ X0 )
      | ( r2_hidden @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PTuGEmAJ7g
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 461 iterations in 0.210s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(t7_xboole_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X10 : $i]:
% 0.45/0.67         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf(t41_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('2', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.67  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X10 : $i]:
% 0.45/0.67         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('6', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('8', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(d5_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | (r2_hidden @ X0 @ X3)
% 0.45/0.67          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ sk_B_1 @ X0)
% 0.45/0.67          | (r2_hidden @ sk_B_1 @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '10'])).
% 0.45/0.67  thf(t3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.67            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.67          | ~ (r2_hidden @ X4 @ X2)
% 0.45/0.67          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.67          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X8 @ X6)
% 0.45/0.67          | ~ (r2_hidden @ X8 @ X9)
% 0.45/0.67          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.67          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.45/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '24'])).
% 0.45/0.67  thf(l24_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X23 : $i, X24 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ (k1_tarski @ X23) @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.67  thf('28', plain, ((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['11', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X10 : $i]:
% 0.45/0.67         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.67          | (r2_hidden @ X4 @ X1)
% 0.45/0.67          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.67         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['29', '31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.45/0.67          | ((sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X10 : $i]:
% 0.45/0.67         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.45/0.67          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.45/0.67          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['34', '37'])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '39'])).
% 0.45/0.67  thf(l32_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         ((r1_tarski @ X11 @ X12)
% 0.45/0.67          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.67        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['42'])).
% 0.45/0.67  thf(l3_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.45/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i]:
% 0.45/0.67         (((X26) = (k1_tarski @ X25))
% 0.45/0.67          | ((X26) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 0.45/0.67      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.67  thf('46', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('48', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['45', '46', '47'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
