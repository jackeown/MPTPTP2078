%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J5MyIVgzpR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 180 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  518 (1650 expanded)
%              Number of equality atoms :   53 ( 218 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('9',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) )
      | ( X29 != X30 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('22',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','23','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['27'])).

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

thf('29',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('34',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('39',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['12','23'])).

thf('40',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('45',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['41','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J5MyIVgzpR
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 81 iterations in 0.021s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.44  thf(d10_xboole_0, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.44  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.19/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.44  thf(d1_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.44         (~ (r1_tarski @ X22 @ X23)
% 0.19/0.44          | (r2_hidden @ X22 @ X24)
% 0.19/0.44          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.44  thf('3', plain,
% 0.19/0.44      (![X22 : $i, X23 : $i]:
% 0.19/0.44         ((r2_hidden @ X22 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X22 @ X23))),
% 0.19/0.44      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.44  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.44  thf(l27_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X27 : $i, X28 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.19/0.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.44  thf('6', plain,
% 0.19/0.44      (![X27 : $i, X28 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.19/0.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.44  thf(t83_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X9 : $i, X10 : $i]:
% 0.19/0.44         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.19/0.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         ((r2_hidden @ X1 @ X0)
% 0.19/0.44          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.44  thf(t20_zfmisc_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.44         ( k1_tarski @ A ) ) <=>
% 0.19/0.44       ( ( A ) != ( B ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.44            ( k1_tarski @ A ) ) <=>
% 0.19/0.44          ( ( A ) != ( B ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      ((((sk_A) = (sk_B))
% 0.19/0.44        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44            != (k1_tarski @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          != (k1_tarski @ sk_A)))
% 0.19/0.44         <= (~
% 0.19/0.44             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))))),
% 0.19/0.44      inference('split', [status(esa)], ['9'])).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      ((((sk_A) != (sk_B))
% 0.19/0.44        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44            = (k1_tarski @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.44       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A)))),
% 0.19/0.44      inference('split', [status(esa)], ['11'])).
% 0.19/0.44  thf('13', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.44      inference('split', [status(esa)], ['9'])).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A)))
% 0.19/0.44         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))))),
% 0.19/0.44      inference('split', [status(esa)], ['11'])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A)))
% 0.19/0.44         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))) & 
% 0.19/0.44             (((sk_A) = (sk_B))))),
% 0.19/0.44      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.44  thf('16', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.44      inference('split', [status(esa)], ['9'])).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_B)))
% 0.19/0.44         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))) & 
% 0.19/0.44             (((sk_A) = (sk_B))))),
% 0.19/0.44      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.44  thf('18', plain,
% 0.19/0.44      (![X9 : $i, X11 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.44  thf('19', plain,
% 0.19/0.44      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.19/0.44         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.19/0.44         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))) & 
% 0.19/0.44             (((sk_A) = (sk_B))))),
% 0.19/0.44      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.44  thf('20', plain,
% 0.19/0.44      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.19/0.44         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44                = (k1_tarski @ sk_A))) & 
% 0.19/0.44             (((sk_A) = (sk_B))))),
% 0.19/0.44      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.44  thf(t16_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.19/0.44          ( ( A ) = ( B ) ) ) ))).
% 0.19/0.44  thf('21', plain,
% 0.19/0.44      (![X29 : $i, X30 : $i]:
% 0.19/0.44         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30))
% 0.19/0.44          | ((X29) != (X30)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.19/0.44  thf('22', plain,
% 0.19/0.44      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.19/0.44      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.44  thf('23', plain,
% 0.19/0.44      (~
% 0.19/0.44       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A))) | 
% 0.19/0.44       ~ (((sk_A) = (sk_B)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.44  thf('24', plain,
% 0.19/0.44      (~
% 0.19/0.44       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A))) | 
% 0.19/0.44       (((sk_A) = (sk_B)))),
% 0.19/0.44      inference('split', [status(esa)], ['9'])).
% 0.19/0.44  thf('25', plain,
% 0.19/0.44      (~
% 0.19/0.44       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44          = (k1_tarski @ sk_A)))),
% 0.19/0.44      inference('sat_resolution*', [status(thm)], ['12', '23', '24'])).
% 0.19/0.44  thf('26', plain,
% 0.19/0.44      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.44         != (k1_tarski @ sk_A))),
% 0.19/0.44      inference('simpl_trail', [status(thm)], ['10', '25'])).
% 0.19/0.44  thf('27', plain,
% 0.19/0.44      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.19/0.44        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['8', '26'])).
% 0.19/0.44  thf('28', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.44      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.44  thf(t3_xboole_0, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.44            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.44       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.44            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.44  thf('29', plain,
% 0.19/0.44      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.44         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.44          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.44          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.44  thf('30', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.44  thf('31', plain,
% 0.19/0.44      (![X0 : $i]: ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['5', '30'])).
% 0.19/0.44  thf('32', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['4', '31'])).
% 0.19/0.44  thf('33', plain,
% 0.19/0.44      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.44         (~ (r2_hidden @ X25 @ X24)
% 0.19/0.44          | (r1_tarski @ X25 @ X23)
% 0.19/0.44          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.44  thf('34', plain,
% 0.19/0.44      (![X23 : $i, X25 : $i]:
% 0.19/0.44         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.44  thf('35', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.44      inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.44  thf('36', plain,
% 0.19/0.44      (![X4 : $i, X6 : $i]:
% 0.19/0.44         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.44  thf('37', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.44  thf('38', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.19/0.44      inference('split', [status(esa)], ['11'])).
% 0.19/0.44  thf('39', plain, (~ (((sk_A) = (sk_B)))),
% 0.19/0.44      inference('sat_resolution*', [status(thm)], ['12', '23'])).
% 0.19/0.44  thf('40', plain, (((sk_A) != (sk_B))),
% 0.19/0.44      inference('simpl_trail', [status(thm)], ['38', '39'])).
% 0.19/0.44  thf('41', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.19/0.44  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.44  thf('43', plain,
% 0.19/0.44      (![X27 : $i, X28 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.19/0.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.44  thf('44', plain,
% 0.19/0.44      (![X27 : $i, X28 : $i]:
% 0.19/0.44         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.19/0.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.44  thf('45', plain,
% 0.19/0.44      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.19/0.44      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.44  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.44  thf('47', plain,
% 0.19/0.44      (![X0 : $i]: ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['5', '30'])).
% 0.19/0.44  thf('48', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.44  thf('49', plain,
% 0.19/0.44      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.44         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.44          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.44          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.44      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.44  thf('50', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.44  thf('51', plain,
% 0.19/0.44      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['43', '50'])).
% 0.19/0.44  thf('52', plain, ((r2_hidden @ sk_A @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.44      inference('sup-', [status(thm)], ['42', '51'])).
% 0.19/0.44  thf('53', plain,
% 0.19/0.44      (![X23 : $i, X25 : $i]:
% 0.19/0.44         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.44  thf('54', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.44      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.44  thf('55', plain, ($false), inference('demod', [status(thm)], ['41', '54'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
