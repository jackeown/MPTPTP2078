%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04mHPwT9HN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:24 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 115 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  658 (1664 expanded)
%              Number of equality atoms :   54 ( 132 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = X0 )
      | ( ( k2_tarski @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k2_tarski @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) )
      | ( ( k2_tarski @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','33'])).

thf('35',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('36',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04mHPwT9HN
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.65/2.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.65/2.87  % Solved by: fo/fo7.sh
% 2.65/2.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.87  % done 1886 iterations in 2.419s
% 2.65/2.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.65/2.87  % SZS output start Refutation
% 2.65/2.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.65/2.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.65/2.87  thf(sk_C_type, type, sk_C: $i).
% 2.65/2.87  thf(sk_B_type, type, sk_B: $i).
% 2.65/2.87  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.65/2.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.65/2.87  thf(t53_zfmisc_1, conjecture,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 2.65/2.87       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 2.65/2.87  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.87    (~( ![A:$i,B:$i,C:$i]:
% 2.65/2.87        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 2.65/2.87          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 2.65/2.87    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 2.65/2.87  thf('0', plain, ((r2_hidden @ sk_C @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(d4_xboole_0, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.65/2.87       ( ![D:$i]:
% 2.65/2.87         ( ( r2_hidden @ D @ C ) <=>
% 2.65/2.87           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.65/2.87  thf('2', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.65/2.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('3', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['2'])).
% 2.65/2.87  thf(d2_tarski, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.65/2.87       ( ![D:$i]:
% 2.65/2.87         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.65/2.87  thf('4', plain,
% 2.65/2.87      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X10 @ X8)
% 2.65/2.87          | ((X10) = (X9))
% 2.65/2.87          | ((X10) = (X6))
% 2.65/2.87          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 2.65/2.87      inference('cnf', [status(esa)], [d2_tarski])).
% 2.65/2.87  thf('5', plain,
% 2.65/2.87      (![X6 : $i, X9 : $i, X10 : $i]:
% 2.65/2.87         (((X10) = (X6))
% 2.65/2.87          | ((X10) = (X9))
% 2.65/2.87          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['4'])).
% 2.65/2.87  thf('6', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (((k2_tarski @ X1 @ X0) = (k3_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 2.65/2.87          | ((sk_D @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0) @ X2) = (X1))
% 2.65/2.87          | ((sk_D @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0) @ X2) = (X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['3', '5'])).
% 2.65/2.87  thf('7', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['2'])).
% 2.65/2.87  thf('8', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.65/2.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('9', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['7', '8'])).
% 2.65/2.87  thf('10', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['9'])).
% 2.65/2.87  thf('11', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['2'])).
% 2.65/2.87  thf('12', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.65/2.87      inference('clc', [status(thm)], ['10', '11'])).
% 2.65/2.87  thf('13', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X0 @ X1)
% 2.65/2.87          | ((sk_D @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 2.65/2.87          | ((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 2.65/2.87          | ((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['6', '12'])).
% 2.65/2.87  thf('14', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (((k2_tarski @ X0 @ X2) = (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 2.65/2.87          | ((sk_D @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 2.65/2.87          | ~ (r2_hidden @ X0 @ X1))),
% 2.65/2.87      inference('simplify', [status(thm)], ['13'])).
% 2.65/2.87  thf('15', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (((sk_D @ (k2_tarski @ sk_A @ X0) @ (k2_tarski @ sk_A @ X0) @ sk_B)
% 2.65/2.87            = (X0))
% 2.65/2.87          | ((k2_tarski @ sk_A @ X0)
% 2.65/2.87              = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['1', '14'])).
% 2.65/2.87  thf('16', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.65/2.87      inference('clc', [status(thm)], ['10', '11'])).
% 2.65/2.87  thf('17', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X0 @ sk_B)
% 2.65/2.87          | ((k2_tarski @ sk_A @ X0)
% 2.65/2.87              = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0)))
% 2.65/2.87          | ((k2_tarski @ sk_A @ X0)
% 2.65/2.87              = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['15', '16'])).
% 2.65/2.87  thf('18', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (((k2_tarski @ sk_A @ X0)
% 2.65/2.87            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0)))
% 2.65/2.87          | ~ (r2_hidden @ X0 @ sk_B))),
% 2.65/2.87      inference('simplify', [status(thm)], ['17'])).
% 2.65/2.87  thf('19', plain,
% 2.65/2.87      (((k2_tarski @ sk_A @ sk_C)
% 2.65/2.87         = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['0', '18'])).
% 2.65/2.87  thf('20', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.65/2.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('21', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['20'])).
% 2.65/2.87  thf('22', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.65/2.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.65/2.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('23', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.65/2.87         (~ (r2_hidden @ X4 @ X3)
% 2.65/2.87          | (r2_hidden @ X4 @ X1)
% 2.65/2.87          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('24', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.65/2.87         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['23'])).
% 2.65/2.87  thf('25', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 2.65/2.87          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 2.65/2.87          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X1))),
% 2.65/2.87      inference('sup-', [status(thm)], ['22', '24'])).
% 2.65/2.87  thf('26', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X0)
% 2.65/2.87          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['25'])).
% 2.65/2.87  thf('27', plain,
% 2.65/2.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.65/2.87         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.65/2.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.65/2.87  thf('28', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 2.65/2.87               (k3_xboole_0 @ X0 @ X2))
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 2.65/2.87          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['26', '27'])).
% 2.65/2.87  thf('29', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 2.65/2.87          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 2.65/2.87               (k3_xboole_0 @ X0 @ X2))
% 2.65/2.87          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['28'])).
% 2.65/2.87  thf('30', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ X1 @ X0)
% 2.65/2.87            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 2.65/2.87          | ((k3_xboole_0 @ X1 @ X0)
% 2.65/2.87              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 2.65/2.87          | ~ (r2_hidden @ 
% 2.65/2.87               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.65/2.87               (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['21', '29'])).
% 2.65/2.87  thf('31', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (r2_hidden @ 
% 2.65/2.87             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.65/2.87             (k3_xboole_0 @ X1 @ X0))
% 2.65/2.87          | ((k3_xboole_0 @ X1 @ X0)
% 2.65/2.87              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['30'])).
% 2.65/2.87  thf('32', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.65/2.87          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.65/2.87      inference('eq_fact', [status(thm)], ['20'])).
% 2.65/2.87  thf('33', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((k3_xboole_0 @ X1 @ X0)
% 2.65/2.87           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 2.65/2.87      inference('clc', [status(thm)], ['31', '32'])).
% 2.65/2.87  thf('34', plain,
% 2.65/2.87      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 2.65/2.87         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 2.65/2.87      inference('sup+', [status(thm)], ['19', '33'])).
% 2.65/2.87  thf('35', plain,
% 2.65/2.87      (((k2_tarski @ sk_A @ sk_C)
% 2.65/2.87         = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['0', '18'])).
% 2.65/2.87  thf('36', plain,
% 2.65/2.87      (((k2_tarski @ sk_A @ sk_C)
% 2.65/2.87         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 2.65/2.87      inference('demod', [status(thm)], ['34', '35'])).
% 2.65/2.87  thf('37', plain,
% 2.65/2.87      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 2.65/2.87         != (k2_tarski @ sk_A @ sk_C))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('38', plain, ($false),
% 2.65/2.87      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 2.65/2.87  
% 2.65/2.87  % SZS output end Refutation
% 2.65/2.87  
% 2.65/2.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
