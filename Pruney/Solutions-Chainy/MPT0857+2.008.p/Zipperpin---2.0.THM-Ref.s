%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cnmdkF4hml

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  329 ( 755 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) )
        = X17 )
      | ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('18',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X15 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C = X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_C = X0 )
      | ~ ( r2_hidden @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('30',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('32',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['25','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cnmdkF4hml
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 136 iterations in 0.090s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(t13_mcart_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.22/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.55         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.55        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.22/0.56          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.56            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t10_mcart_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.56         ((r2_hidden @ (k2_mcart_1 @ X19) @ X21)
% 0.22/0.56          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.56  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.56  thf(d5_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.56       ( ![D:$i]:
% 0.22/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.56          | (r2_hidden @ X0 @ X2)
% 0.22/0.56          | (r2_hidden @ X0 @ X3)
% 0.22/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ X0 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 0.22/0.56          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.22/0.56             (k4_xboole_0 @ (k1_tarski @ sk_C) @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.56  thf(t64_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.56         (((X12) != (X14))
% 0.22/0.56          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14))))),
% 0.22/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]:
% 0.22/0.56         ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.56  thf('9', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.56  thf(t65_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ X17 @ (k1_tarski @ X18)) = (X17))
% 0.22/0.56          | (r2_hidden @ X18 @ X17))),
% 0.22/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.56          | (r2_hidden @ X1 @ X0)
% 0.22/0.56          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ sk_C @ X0) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '13'])).
% 0.22/0.56  thf('15', plain, ((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '14'])).
% 0.22/0.56  thf('16', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ sk_C @ X0) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '13'])).
% 0.22/0.56  thf('18', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))),
% 0.22/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.22/0.56         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X15)))
% 0.22/0.56          | ((X12) = (X15))
% 0.22/0.56          | ~ (r2_hidden @ X12 @ X13))),
% 0.22/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((sk_C) = (X0))
% 0.22/0.56          | (r2_hidden @ sk_C @ 
% 0.22/0.56             (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ X0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      (![X0 : $i]: (((sk_C) = (X0)) | ~ (r2_hidden @ sk_C @ (k1_tarski @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain, (((sk_C) = (k2_mcart_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['15', '22'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.22/0.56        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.56      inference('split', [status(esa)], ['24'])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.56         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.22/0.56          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.56  thf('28', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.22/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.22/0.56         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.22/0.56      inference('split', [status(esa)], ['24'])).
% 0.22/0.56  thf('30', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.22/0.56       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.22/0.56      inference('split', [status(esa)], ['24'])).
% 0.22/0.56  thf('32', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['25', '32'])).
% 0.22/0.56  thf('34', plain, ($false),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['23', '33'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
