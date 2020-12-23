%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1KJ9z34hIR

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 266 expanded)
%              Number of leaves         :   19 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  595 (2901 expanded)
%              Number of equality atoms :   58 ( 326 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t34_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
      <=> ( ( A = C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D_1 )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
    | ( sk_B != sk_D_1 )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X9 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('26',plain,
    ( ( sk_B = sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = sk_D_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','21','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','30'])).

thf('32',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','21','29','33'])).

thf('35',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B = sk_D_1 )
   <= ( sk_B = sk_D_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('39',plain,(
    sk_B = sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['2','21','29','38'])).

thf('40',plain,(
    sk_B = sk_D_1 ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('44',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['41','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1KJ9z34hIR
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 92 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(t34_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @
% 0.20/0.49         ( k4_tarski @ A @ B ) @ 
% 0.20/0.49         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( r2_hidden @
% 0.20/0.49            ( k4_tarski @ A @ B ) @ 
% 0.20/0.49            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_B) != (sk_D_1))
% 0.20/0.49        | ((sk_A) != (sk_C))
% 0.20/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))) | 
% 0.20/0.49       ~ (((sk_B) = (sk_D_1))) | ~ (((sk_A) = (sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((sk_A) = (sk_C))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(l54_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         ((r2_hidden @ X16 @ X17)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t77_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X7 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.20/0.49  thf(t84_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X13 @ X13 @ X13 @ X13 @ X14 @ X15)
% 0.20/0.49           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.20/0.49  thf(t79_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.20/0.49       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X9 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.49           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 0.20/0.49           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf(t76_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X6 : $i]: ((k1_enumset1 @ X6 @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.20/0.49  thf('13', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(d2_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X4) = (X3))
% 0.20/0.49          | ((X4) = (X0))
% 0.20/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (((X4) = (X0))
% 0.20/0.49          | ((X4) = (X3))
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((sk_A) = (sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.49  thf('19', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((((sk_A) = (sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         ((r2_hidden @ X18 @ X19)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((sk_B) != (sk_B)))
% 0.20/0.49         <= (~ (((sk_B) = (sk_D_1))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '21', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '30'])).
% 0.20/0.49  thf('32', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((((sk_A) = (sk_C))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('34', plain, ((((sk_A) = (sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '21', '29', '33'])).
% 0.20/0.49  thf('35', plain, (((sk_A) = (sk_C))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain, ((((sk_B) = (sk_D_1))) <= ((((sk_B) = (sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['36'])).
% 0.20/0.49  thf('39', plain, ((((sk_B) = (sk_D_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '21', '29', '38'])).
% 0.20/0.49  thf('40', plain, (((sk_B) = (sk_D_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '35', '40'])).
% 0.20/0.49  thf('42', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((X1) != (X0))
% 0.20/0.49          | (r2_hidden @ X1 @ X2)
% 0.20/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.49  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '44'])).
% 0.20/0.49  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '44'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X20))
% 0.20/0.49          | ~ (r2_hidden @ X18 @ X20)
% 0.20/0.49          | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.49  thf('50', plain, ($false), inference('demod', [status(thm)], ['41', '49'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
