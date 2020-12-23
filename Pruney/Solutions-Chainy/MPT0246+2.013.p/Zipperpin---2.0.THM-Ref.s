%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MgUDXqX3KD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:15 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  357 ( 527 expanded)
%              Number of equality atoms :   47 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
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

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X25: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ X27 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ( X28 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['17','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MgUDXqX3KD
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:59:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.53  % Solved by: fo/fo7.sh
% 0.18/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.53  % done 118 iterations in 0.068s
% 0.18/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.53  % SZS output start Refutation
% 0.18/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.53  thf(t7_xboole_0, axiom,
% 0.18/0.53    (![A:$i]:
% 0.18/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.18/0.53  thf('0', plain,
% 0.18/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.18/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.53  thf(t41_zfmisc_1, conjecture,
% 0.18/0.53    (![A:$i,B:$i]:
% 0.18/0.53     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.53          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.18/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.53    (~( ![A:$i,B:$i]:
% 0.18/0.53        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.53             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.18/0.53    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.18/0.53  thf('1', plain,
% 0.18/0.53      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.18/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.53  thf('2', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.53  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.53  thf('4', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.18/0.53      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.18/0.53  thf('5', plain,
% 0.18/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.18/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.53  thf('6', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.18/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.18/0.53  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.53  thf('8', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.18/0.53      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.18/0.53  thf(l35_zfmisc_1, axiom,
% 0.18/0.53    (![A:$i,B:$i]:
% 0.18/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.53       ( r2_hidden @ A @ B ) ))).
% 0.18/0.53  thf('9', plain,
% 0.18/0.53      (![X25 : $i, X27 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ (k1_tarski @ X25) @ X27) = (k1_xboole_0))
% 0.18/0.53          | ~ (r2_hidden @ X25 @ X27))),
% 0.18/0.53      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.18/0.53  thf('10', plain,
% 0.18/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.18/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.53  thf(l32_xboole_1, axiom,
% 0.18/0.53    (![A:$i,B:$i]:
% 0.18/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.53  thf('11', plain,
% 0.18/0.53      (![X12 : $i, X13 : $i]:
% 0.18/0.53         ((r1_tarski @ X12 @ X13)
% 0.18/0.53          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.18/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.53  thf('12', plain,
% 0.18/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.53        | (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.18/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.53  thf('13', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.18/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.53  thf(d10_xboole_0, axiom,
% 0.18/0.53    (![A:$i,B:$i]:
% 0.18/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.53  thf('14', plain,
% 0.18/0.53      (![X9 : $i, X11 : $i]:
% 0.18/0.53         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.18/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.53  thf('15', plain,
% 0.18/0.53      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))
% 0.18/0.53        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.53  thf('16', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.18/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.53  thf('17', plain, (~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.18/0.53      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.18/0.53  thf('18', plain,
% 0.18/0.53      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.18/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.53  thf('19', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.18/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.18/0.53  thf('20', plain,
% 0.18/0.53      (![X12 : $i, X14 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.18/0.53          | ~ (r1_tarski @ X12 @ X14))),
% 0.18/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.53  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.18/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.53  thf('22', plain,
% 0.18/0.53      (![X25 : $i, X26 : $i]:
% 0.18/0.53         ((r2_hidden @ X25 @ X26)
% 0.18/0.53          | ((k4_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0)))),
% 0.18/0.53      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.18/0.53  thf('23', plain,
% 0.18/0.53      (![X0 : $i]:
% 0.18/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.53          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.53  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.18/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.18/0.53  thf('25', plain,
% 0.18/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.18/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.53  thf(d5_xboole_0, axiom,
% 0.18/0.53    (![A:$i,B:$i,C:$i]:
% 0.18/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.18/0.53       ( ![D:$i]:
% 0.18/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.18/0.53  thf('26', plain,
% 0.18/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.18/0.53          | (r2_hidden @ X4 @ X1)
% 0.18/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.53  thf('27', plain,
% 0.18/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.18/0.53         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.18/0.53  thf('28', plain,
% 0.18/0.53      (![X0 : $i, X1 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.18/0.53          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.18/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.18/0.53  thf('29', plain,
% 0.18/0.53      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ((X28) = (sk_B_1)))),
% 0.18/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.53  thf('30', plain,
% 0.18/0.53      (![X0 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.18/0.53          | ((sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B_1)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.18/0.53  thf('31', plain,
% 0.18/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.18/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.53  thf('32', plain,
% 0.18/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.18/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.18/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.53  thf('33', plain,
% 0.18/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.18/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.18/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.18/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.18/0.53  thf('34', plain,
% 0.18/0.53      (![X0 : $i, X1 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.18/0.53          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.18/0.53      inference('sup-', [status(thm)], ['31', '33'])).
% 0.18/0.53  thf('35', plain,
% 0.18/0.53      (![X0 : $i]:
% 0.18/0.53         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.18/0.53          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.18/0.53          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['30', '34'])).
% 0.18/0.53  thf('36', plain,
% 0.18/0.53      (![X0 : $i]:
% 0.18/0.53         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.18/0.53          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.18/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.18/0.53  thf('37', plain,
% 0.18/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.18/0.53      inference('sup-', [status(thm)], ['24', '36'])).
% 0.18/0.53  thf('38', plain,
% 0.18/0.53      (![X12 : $i, X13 : $i]:
% 0.18/0.53         ((r1_tarski @ X12 @ X13)
% 0.18/0.53          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.18/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.53  thf('39', plain,
% 0.18/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.53        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.18/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.53  thf('40', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.18/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.18/0.53  thf('41', plain, ($false), inference('demod', [status(thm)], ['17', '40'])).
% 0.18/0.53  
% 0.18/0.53  % SZS output end Refutation
% 0.18/0.53  
% 0.18/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
