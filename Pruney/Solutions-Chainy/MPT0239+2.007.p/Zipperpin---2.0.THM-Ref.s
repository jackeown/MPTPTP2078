%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3lc1t7pDC4

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 236 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  560 (2705 expanded)
%              Number of equality atoms :   52 ( 281 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('22',plain,
    ( ( sk_B = sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = sk_D_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','25','29'])).

thf('31',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = sk_D_1 )
   <= ( sk_B = sk_D_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    sk_B = sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','35'])).

thf('37',plain,(
    sk_B = sk_D_1 ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','31','32','37'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('40',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['38','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3lc1t7pDC4
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 180 iterations in 0.081s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(t34_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( r2_hidden @
% 0.20/0.53         ( k4_tarski @ A @ B ) @ 
% 0.20/0.53         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ( r2_hidden @
% 0.20/0.53            ( k4_tarski @ A @ B ) @ 
% 0.20/0.53            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.53          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((sk_B) != (sk_D_1))
% 0.20/0.53        | ((sk_A) != (sk_C))
% 0.20/0.53        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))) | 
% 0.20/0.53       ~ (((sk_B) = (sk_D_1))) | ~ (((sk_A) = (sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((((sk_A) = (sk_C))
% 0.20/0.53        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf(l54_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((r2_hidden @ X10 @ X11)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(t20_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.20/0.53            = (k1_tarski @ X16))
% 0.20/0.53          | ((X16) = (X17)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf(l33_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.53          | ((k4_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_tarski @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.53          | ((X0) = (X1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((((sk_A) = (sk_C)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.53  thf('12', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((sk_A) != (sk_A)))
% 0.20/0.53         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((sk_A) = (sk_C))) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((((sk_A) = (sk_C)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('17', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_D_1))))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((r2_hidden @ X12 @ X13)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((sk_B) = (sk_D_1)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_B) != (sk_B)))
% 0.20/0.53         <= (~ (((sk_B) = (sk_D_1))) & 
% 0.20/0.53             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.20/0.53  thf('28', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((sk_A) = (sk_C))) | 
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf('30', plain, ((((sk_A) = (sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '29'])).
% 0.20/0.53  thf('31', plain, (((sk_A) = (sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.53  thf('32', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((sk_B) = (sk_D_1))
% 0.20/0.53        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain, ((((sk_B) = (sk_D_1))) <= ((((sk_B) = (sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['33'])).
% 0.20/0.53  thf('36', plain, ((((sk_B) = (sk_D_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '35'])).
% 0.20/0.53  thf('37', plain, (((sk_B) = (sk_D_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.53          (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '31', '32', '37'])).
% 0.20/0.53  thf(d2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((X1) != (X0))
% 0.20/0.53          | (r2_hidden @ X1 @ X2)
% 0.20/0.53          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.20/0.53         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.20/0.53          | ~ (r2_hidden @ X12 @ X14)
% 0.20/0.53          | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.20/0.53             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 0.20/0.53          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.53  thf('47', plain, ($false), inference('demod', [status(thm)], ['38', '46'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
