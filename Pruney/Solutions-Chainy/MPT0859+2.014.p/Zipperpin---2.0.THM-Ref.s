%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7B8wgyy9j

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  486 (1076 expanded)
%              Number of equality atoms :   35 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ( X12
        = ( k4_xboole_0 @ X12 @ ( k2_tarski @ X11 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X3 @ X2 ) )
      | ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('14',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_mcart_1 @ X22 )
        = X21 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ ( k1_tarski @ X21 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_mcart_1 @ ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('29',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['23','29'])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_mcart_1 @ X22 )
        = X21 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ ( k1_tarski @ X21 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_B @ ( k2_mcart_1 @ sk_A ) ) )
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('37',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['25'])).

thf('39',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('40',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['27','39'])).

thf('41',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['38','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7B8wgyy9j
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:14 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.89/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.12  % Solved by: fo/fo7.sh
% 0.89/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.12  % done 1104 iterations in 0.663s
% 0.89/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.12  % SZS output start Refutation
% 0.89/1.12  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.89/1.12  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.89/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.12  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.12  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.89/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.12  thf(t69_enumset1, axiom,
% 0.89/1.12    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.89/1.12  thf('0', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.89/1.12      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.12  thf(t15_mcart_1, conjecture,
% 0.89/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.12     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.89/1.12       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.89/1.12         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.89/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.12    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.12        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.89/1.12          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.89/1.12            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 0.89/1.12    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 0.89/1.12  thf('1', plain,
% 0.89/1.12      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t10_mcart_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.89/1.12       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.89/1.12         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.12  thf('2', plain,
% 0.89/1.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.12         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.89/1.12          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.12  thf('3', plain,
% 0.89/1.12      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.12  thf(t144_zfmisc_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.89/1.12          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.89/1.12  thf('4', plain,
% 0.89/1.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.89/1.12         ((r2_hidden @ X11 @ X12)
% 0.89/1.12          | (r2_hidden @ X13 @ X12)
% 0.89/1.12          | ((X12) = (k4_xboole_0 @ X12 @ (k2_tarski @ X11 @ X13))))),
% 0.89/1.12      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.89/1.12  thf(t72_zfmisc_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.89/1.12       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.89/1.12  thf('5', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.12         (~ (r2_hidden @ X14 @ X15)
% 0.89/1.12          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 0.89/1.12              != (k2_tarski @ X14 @ X16)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.89/1.12  thf('6', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.12         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.89/1.12          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.89/1.12          | (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 0.89/1.12          | ~ (r2_hidden @ X1 @ (k2_tarski @ X3 @ X2)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.12  thf('7', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.12         (~ (r2_hidden @ X1 @ (k2_tarski @ X3 @ X2))
% 0.89/1.12          | (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 0.89/1.12          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.89/1.12      inference('simplify', [status(thm)], ['6'])).
% 0.89/1.12  thf('8', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((r2_hidden @ sk_C @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.89/1.12          | (r2_hidden @ sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['3', '7'])).
% 0.89/1.12  thf('9', plain,
% 0.89/1.12      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.89/1.12        | (r2_hidden @ sk_B @ 
% 0.89/1.12           (k2_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['0', '8'])).
% 0.89/1.12  thf('10', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.89/1.12      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.12  thf('11', plain,
% 0.89/1.12      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.89/1.12        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.12  thf('12', plain,
% 0.89/1.12      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('13', plain,
% 0.89/1.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.12         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.89/1.12          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.12  thf('14', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)),
% 0.89/1.12      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.12  thf(l54_zfmisc_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.12     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.89/1.12       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.89/1.12  thf('15', plain,
% 0.89/1.12      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.89/1.12         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.89/1.12          | ~ (r2_hidden @ X8 @ X10)
% 0.89/1.12          | ~ (r2_hidden @ X6 @ X7))),
% 0.89/1.12      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.89/1.12  thf('16', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         (~ (r2_hidden @ X1 @ X0)
% 0.89/1.12          | (r2_hidden @ (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ 
% 0.89/1.12             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.12  thf('17', plain,
% 0.89/1.12      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.89/1.12        | (r2_hidden @ (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_A)) @ 
% 0.89/1.12           (k2_zfmisc_1 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ sk_D)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['11', '16'])).
% 0.89/1.12  thf(t12_mcart_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.89/1.12       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.89/1.12         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.12  thf('18', plain,
% 0.89/1.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.89/1.12         (((k1_mcart_1 @ X22) = (X21))
% 0.89/1.12          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ (k1_tarski @ X21) @ X23)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.89/1.12  thf('19', plain,
% 0.89/1.12      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.89/1.12        | ((k1_mcart_1 @ (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_A)))
% 0.89/1.12            = (k1_mcart_1 @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.12  thf(t7_mcart_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.89/1.12       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.89/1.12  thf('20', plain,
% 0.89/1.12      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.89/1.12      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.89/1.12  thf('21', plain,
% 0.89/1.12      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.89/1.12        | ((sk_C) = (k1_mcart_1 @ sk_A)))),
% 0.89/1.12      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.12  thf('22', plain,
% 0.89/1.12      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 0.89/1.12        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('23', plain,
% 0.89/1.12      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.89/1.12         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.89/1.12      inference('split', [status(esa)], ['22'])).
% 0.89/1.12  thf('24', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)),
% 0.89/1.12      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.12  thf('25', plain,
% 0.89/1.12      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.89/1.12        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('26', plain,
% 0.89/1.12      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))
% 0.89/1.12         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)))),
% 0.89/1.12      inference('split', [status(esa)], ['25'])).
% 0.89/1.12  thf('27', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.89/1.12      inference('sup-', [status(thm)], ['24', '26'])).
% 0.89/1.12  thf('28', plain,
% 0.89/1.12      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.89/1.12       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.89/1.12      inference('split', [status(esa)], ['22'])).
% 0.89/1.12  thf('29', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.89/1.12      inference('sat_resolution*', [status(thm)], ['27', '28'])).
% 0.89/1.12  thf('30', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.89/1.12      inference('simpl_trail', [status(thm)], ['23', '29'])).
% 0.89/1.12  thf('31', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.89/1.12      inference('simplify_reflect-', [status(thm)], ['21', '30'])).
% 0.89/1.12  thf('32', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         (~ (r2_hidden @ X1 @ X0)
% 0.89/1.12          | (r2_hidden @ (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ 
% 0.89/1.12             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.12  thf('33', plain,
% 0.89/1.12      ((r2_hidden @ (k4_tarski @ sk_B @ (k2_mcart_1 @ sk_A)) @ 
% 0.89/1.12        (k2_zfmisc_1 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ sk_D))),
% 0.89/1.12      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.12  thf('34', plain,
% 0.89/1.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.89/1.12         (((k1_mcart_1 @ X22) = (X21))
% 0.89/1.12          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ (k1_tarski @ X21) @ X23)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.89/1.12  thf('35', plain,
% 0.89/1.12      (((k1_mcart_1 @ (k4_tarski @ sk_B @ (k2_mcart_1 @ sk_A)))
% 0.89/1.12         = (k1_mcart_1 @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.12  thf('36', plain,
% 0.89/1.12      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.89/1.12      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.89/1.12  thf('37', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('38', plain,
% 0.89/1.12      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.89/1.12         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.89/1.12      inference('split', [status(esa)], ['25'])).
% 0.89/1.12  thf('39', plain,
% 0.89/1.12      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.89/1.12       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.89/1.12      inference('split', [status(esa)], ['25'])).
% 0.89/1.12  thf('40', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.89/1.12      inference('sat_resolution*', [status(thm)], ['27', '39'])).
% 0.89/1.12  thf('41', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.89/1.12      inference('simpl_trail', [status(thm)], ['38', '40'])).
% 0.89/1.12  thf('42', plain, ($false),
% 0.89/1.12      inference('simplify_reflect-', [status(thm)], ['37', '41'])).
% 0.89/1.12  
% 0.89/1.12  % SZS output end Refutation
% 0.89/1.12  
% 0.89/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
