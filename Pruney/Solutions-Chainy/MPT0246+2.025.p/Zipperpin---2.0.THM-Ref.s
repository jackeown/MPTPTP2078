%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Re5cZXPWbm

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:17 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   70 (  89 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  474 ( 736 expanded)
%              Number of equality atoms :   40 (  68 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_A )
      | ( X30 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ( ( sk_C @ sk_A @ X0 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('28',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_A )
      | ( X30 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('39',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('42',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X25 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( ( k4_xboole_0 @ X15 @ X14 )
       != ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('47',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    k1_xboole_0
 != ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Re5cZXPWbm
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 454 iterations in 0.225s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(t3_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.47/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.68            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf(t41_zfmisc_1, conjecture,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i]:
% 0.47/0.68        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X30 : $i]: (~ (r2_hidden @ X30 @ sk_A) | ((X30) = (sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X0 @ sk_A) | ((sk_C @ sk_A @ X0) = (sk_B_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((r2_hidden @ sk_B_1 @ X0)
% 0.47/0.68          | (r1_xboole_0 @ X0 @ sk_A)
% 0.47/0.68          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.47/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_A) | (r2_hidden @ sk_B_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf(d5_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.68       ( ![D:$i]:
% 0.47/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.68          | ~ (r2_hidden @ X4 @ X2)
% 0.47/0.68          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.68          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.47/0.68          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['7', '9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.68          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['6', '10'])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.47/0.68      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X8 @ X6)
% 0.47/0.68          | ~ (r2_hidden @ X8 @ X9)
% 0.47/0.68          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X1 @ X0)
% 0.47/0.68          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.47/0.68          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.47/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X0 @ X1)
% 0.47/0.68          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.47/0.68          | (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['13', '16'])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['12', '18'])).
% 0.47/0.68  thf(l24_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X28) @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_B_1)) @ sk_A)),
% 0.47/0.68      inference('sup-', [status(thm)], ['5', '21'])).
% 0.47/0.68  thf(t7_xboole_0, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (![X10 : $i]:
% 0.47/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.68          | (r2_hidden @ X4 @ X1)
% 0.47/0.68          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.68  thf('25', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.68         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.68  thf('26', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.47/0.68          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['23', '25'])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      (![X10 : $i]:
% 0.47/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X8 @ X6)
% 0.47/0.68          | ~ (r2_hidden @ X8 @ X9)
% 0.47/0.68          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((X0) = (k1_xboole_0))
% 0.47/0.68          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.47/0.68          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.68  thf('30', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.47/0.68          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.68          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['26', '29'])).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.68          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['22', '31'])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      (![X10 : $i]:
% 0.47/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X30 : $i]: (~ (r2_hidden @ X30 @ sk_A) | ((X30) = (sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('35', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('37', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X10 : $i]:
% 0.47/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.68  thf('39', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.68  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('41', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.47/0.68  thf(l1_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      (![X25 : $i, X27 : $i]:
% 0.47/0.68         ((r1_tarski @ (k1_tarski @ X25) @ X27) | ~ (r2_hidden @ X25 @ X27))),
% 0.47/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.68  thf('43', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.47/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.68  thf(l32_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X11 : $i, X13 : $i]:
% 0.47/0.68         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.47/0.68          | ~ (r1_tarski @ X11 @ X13))),
% 0.47/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.68  thf(t32_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.47/0.68       ( ( A ) = ( B ) ) ))).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (((X15) = (X14))
% 0.47/0.68          | ((k4_xboole_0 @ X15 @ X14) != (k4_xboole_0 @ X14 @ X15)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.47/0.68        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.68  thf('48', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('49', plain,
% 0.47/0.68      (((k1_xboole_0) != (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.47/0.68  thf('50', plain, ($false),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['32', '49'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
