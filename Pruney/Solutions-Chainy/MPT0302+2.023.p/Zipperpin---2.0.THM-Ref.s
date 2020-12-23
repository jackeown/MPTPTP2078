%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7ZYuCR05P

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 122 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  424 (1042 expanded)
%              Number of equality atoms :   25 (  97 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,
    ( ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('23',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_2 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('42',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7ZYuCR05P
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.21/2.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.21/2.39  % Solved by: fo/fo7.sh
% 2.21/2.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.39  % done 1891 iterations in 1.932s
% 2.21/2.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.21/2.39  % SZS output start Refutation
% 2.21/2.39  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.21/2.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.21/2.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.21/2.39  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.39  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 2.21/2.39  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.21/2.39  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.21/2.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.39  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.21/2.39  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.21/2.39  thf('0', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 2.21/2.39      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.21/2.39  thf(d8_xboole_0, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( r2_xboole_0 @ A @ B ) <=>
% 2.21/2.39       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 2.21/2.39  thf('1', plain,
% 2.21/2.39      (![X4 : $i, X6 : $i]:
% 2.21/2.39         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 2.21/2.39      inference('cnf', [status(esa)], [d8_xboole_0])).
% 2.21/2.39  thf('2', plain,
% 2.21/2.39      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['0', '1'])).
% 2.21/2.39  thf(t6_xboole_0, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 2.21/2.39          ( ![C:$i]:
% 2.21/2.39            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 2.21/2.39  thf('3', plain,
% 2.21/2.39      (![X11 : $i, X12 : $i]:
% 2.21/2.39         (~ (r2_xboole_0 @ X11 @ X12)
% 2.21/2.39          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 2.21/2.39      inference('cnf', [status(esa)], [t6_xboole_0])).
% 2.21/2.39  thf('4', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         (((k1_xboole_0) = (X0))
% 2.21/2.39          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['2', '3'])).
% 2.21/2.39  thf(d3_tarski, axiom,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( r1_tarski @ A @ B ) <=>
% 2.21/2.39       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.21/2.39  thf('5', plain,
% 2.21/2.39      (![X1 : $i, X3 : $i]:
% 2.21/2.39         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.21/2.39      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.39  thf(l54_zfmisc_1, axiom,
% 2.21/2.39    (![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.39     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.21/2.39       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.21/2.39  thf('6', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 2.21/2.39         ((r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X26))
% 2.21/2.39          | ~ (r2_hidden @ X24 @ X26)
% 2.21/2.39          | ~ (r2_hidden @ X22 @ X23))),
% 2.21/2.39      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.21/2.39  thf('7', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.21/2.39         ((r1_tarski @ X0 @ X1)
% 2.21/2.39          | ~ (r2_hidden @ X3 @ X2)
% 2.21/2.39          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 2.21/2.39             (k2_zfmisc_1 @ X2 @ X0)))),
% 2.21/2.39      inference('sup-', [status(thm)], ['5', '6'])).
% 2.21/2.39  thf('8', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (((k1_xboole_0) = (X0))
% 2.21/2.39          | (r2_hidden @ 
% 2.21/2.39             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 2.21/2.39             (k2_zfmisc_1 @ X0 @ X1))
% 2.21/2.39          | (r1_tarski @ X1 @ X2))),
% 2.21/2.39      inference('sup-', [status(thm)], ['4', '7'])).
% 2.21/2.39  thf(t114_zfmisc_1, conjecture,
% 2.21/2.39    (![A:$i,B:$i]:
% 2.21/2.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 2.21/2.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.21/2.39         ( ( A ) = ( B ) ) ) ))).
% 2.21/2.39  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.39    (~( ![A:$i,B:$i]:
% 2.21/2.39        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 2.21/2.39          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.21/2.39            ( ( A ) = ( B ) ) ) ) )),
% 2.21/2.39    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 2.21/2.39  thf('9', plain,
% 2.21/2.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('10', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.21/2.39         ((r2_hidden @ X24 @ X25)
% 2.21/2.39          | ~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X25)))),
% 2.21/2.39      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.21/2.39  thf('11', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]:
% 2.21/2.39         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.21/2.39          | (r2_hidden @ X0 @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['9', '10'])).
% 2.21/2.39  thf('12', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         ((r1_tarski @ sk_B @ X0)
% 2.21/2.39          | ((k1_xboole_0) = (sk_A))
% 2.21/2.39          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['8', '11'])).
% 2.21/2.39  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('14', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 2.21/2.39      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 2.21/2.39  thf('15', plain,
% 2.21/2.39      (![X1 : $i, X3 : $i]:
% 2.21/2.39         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.21/2.39      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.39  thf('16', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['14', '15'])).
% 2.21/2.39  thf('17', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.21/2.39      inference('simplify', [status(thm)], ['16'])).
% 2.21/2.39  thf('18', plain,
% 2.21/2.39      (![X4 : $i, X6 : $i]:
% 2.21/2.39         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 2.21/2.39      inference('cnf', [status(esa)], [d8_xboole_0])).
% 2.21/2.39  thf('19', plain, ((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['17', '18'])).
% 2.21/2.39  thf('20', plain, (((sk_A) != (sk_B))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('21', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 2.21/2.39      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 2.21/2.39  thf('22', plain,
% 2.21/2.39      (![X11 : $i, X12 : $i]:
% 2.21/2.39         (~ (r2_xboole_0 @ X11 @ X12)
% 2.21/2.39          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 2.21/2.39      inference('cnf', [status(esa)], [t6_xboole_0])).
% 2.21/2.39  thf('23', plain, ((r2_hidden @ (sk_C_2 @ sk_A @ sk_B) @ sk_A)),
% 2.21/2.39      inference('sup-', [status(thm)], ['21', '22'])).
% 2.21/2.39  thf('24', plain,
% 2.21/2.39      (![X1 : $i, X3 : $i]:
% 2.21/2.39         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.21/2.39      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.39  thf('25', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         (((k1_xboole_0) = (X0))
% 2.21/2.39          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 2.21/2.39      inference('sup-', [status(thm)], ['2', '3'])).
% 2.21/2.39  thf('26', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 2.21/2.39         ((r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X26))
% 2.21/2.39          | ~ (r2_hidden @ X24 @ X26)
% 2.21/2.39          | ~ (r2_hidden @ X22 @ X23))),
% 2.21/2.39      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.21/2.39  thf('27', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (((k1_xboole_0) = (X0))
% 2.21/2.39          | ~ (r2_hidden @ X2 @ X1)
% 2.21/2.39          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ 
% 2.21/2.39             (k2_zfmisc_1 @ X1 @ X0)))),
% 2.21/2.39      inference('sup-', [status(thm)], ['25', '26'])).
% 2.21/2.39  thf('28', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         ((r1_tarski @ X0 @ X1)
% 2.21/2.39          | (r2_hidden @ 
% 2.21/2.39             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_2 @ X2 @ k1_xboole_0)) @ 
% 2.21/2.39             (k2_zfmisc_1 @ X0 @ X2))
% 2.21/2.39          | ((k1_xboole_0) = (X2)))),
% 2.21/2.39      inference('sup-', [status(thm)], ['24', '27'])).
% 2.21/2.39  thf('29', plain,
% 2.21/2.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('30', plain,
% 2.21/2.39      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.21/2.39         ((r2_hidden @ X22 @ X23)
% 2.21/2.39          | ~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X25)))),
% 2.21/2.39      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.21/2.39  thf('31', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i]:
% 2.21/2.39         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.21/2.39          | (r2_hidden @ X1 @ sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['29', '30'])).
% 2.21/2.39  thf('32', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         (((k1_xboole_0) = (sk_B))
% 2.21/2.39          | (r1_tarski @ sk_A @ X0)
% 2.21/2.39          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['28', '31'])).
% 2.21/2.39  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 2.21/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.39  thf('34', plain,
% 2.21/2.39      (![X0 : $i]:
% 2.21/2.39         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 2.21/2.39      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 2.21/2.39  thf('35', plain,
% 2.21/2.39      (![X1 : $i, X3 : $i]:
% 2.21/2.39         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.21/2.39      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.39  thf('36', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 2.21/2.39      inference('sup-', [status(thm)], ['34', '35'])).
% 2.21/2.39  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.21/2.39      inference('simplify', [status(thm)], ['36'])).
% 2.21/2.39  thf('38', plain,
% 2.21/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.39         (~ (r2_hidden @ X0 @ X1)
% 2.21/2.39          | (r2_hidden @ X0 @ X2)
% 2.21/2.39          | ~ (r1_tarski @ X1 @ X2))),
% 2.21/2.39      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.39  thf('39', plain,
% 2.21/2.39      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 2.21/2.39      inference('sup-', [status(thm)], ['37', '38'])).
% 2.21/2.39  thf('40', plain, ((r2_hidden @ (sk_C_2 @ sk_A @ sk_B) @ sk_B)),
% 2.21/2.39      inference('sup-', [status(thm)], ['23', '39'])).
% 2.21/2.39  thf('41', plain,
% 2.21/2.39      (![X11 : $i, X12 : $i]:
% 2.21/2.39         (~ (r2_xboole_0 @ X11 @ X12)
% 2.21/2.39          | ~ (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X11))),
% 2.21/2.39      inference('cnf', [status(esa)], [t6_xboole_0])).
% 2.21/2.39  thf('42', plain, (~ (r2_xboole_0 @ sk_B @ sk_A)),
% 2.21/2.39      inference('sup-', [status(thm)], ['40', '41'])).
% 2.21/2.39  thf('43', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 2.21/2.39      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 2.21/2.39  thf('44', plain, ($false), inference('demod', [status(thm)], ['42', '43'])).
% 2.21/2.39  
% 2.21/2.39  % SZS output end Refutation
% 2.21/2.39  
% 2.24/2.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
