%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYRdXDM1r8

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  609 (1029 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t128_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
      <=> ( ( A = C )
          & ( r2_hidden @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X8 )
        = X8 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t10_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( ( k2_tarski @ A @ B )
          = ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 = X20 )
      | ( X21 = X22 )
      | ( ( k2_tarski @ X21 @ X23 )
       != ( k2_tarski @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X1 )
       != ( k1_tarski @ X0 ) )
      | ( X2 = X0 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = X0 )
      | ( ( k2_tarski @ X2 @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_C )
         != ( k1_tarski @ X0 ) )
        | ( sk_A = X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t45_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t45_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['29','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['20'])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['33'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','41','42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYRdXDM1r8
% 0.12/0.35  % Computer   : n006.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:25:08 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 119 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t128_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @
% 0.21/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( r2_hidden @
% 0.21/0.51            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.51          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((((sk_A) = (sk_C))
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((((sk_A) = (sk_C))) | 
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(l54_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((r2_hidden @ X10 @ X11)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(l22_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.51       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ (k1_tarski @ X9) @ X8) = (X8))
% 0.21/0.51          | ~ (r2_hidden @ X9 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.21/0.51          = (k1_tarski @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t41_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_tarski @ A @ B ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((k2_tarski @ X5 @ X6)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.21/0.51           = (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.21/0.51           = (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((k2_tarski @ X5 @ X6)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9', '12'])).
% 0.21/0.51  thf(t69_enumset1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.51  thf('14', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf(t10_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ~( ( ( k2_tarski @ A @ B ) = ( k2_tarski @ C @ D ) ) & 
% 0.21/0.51          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (((X21) = (X20))
% 0.21/0.51          | ((X21) = (X22))
% 0.21/0.51          | ((k2_tarski @ X21 @ X23) != (k2_tarski @ X20 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_zfmisc_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k2_tarski @ X2 @ X1) != (k1_tarski @ X0))
% 0.21/0.51          | ((X2) = (X0))
% 0.21/0.51          | ((X2) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X2) = (X0)) | ((k2_tarski @ X2 @ X1) != (k1_tarski @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_tarski @ sk_C) != (k1_tarski @ X0)) | ((sk_A) = (X0))))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((((sk_A) = (sk_C)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.21/0.51        | ((sk_A) != (sk_C))
% 0.21/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((((sk_A) != (sk_A)))
% 0.21/0.51         <= (~ (((sk_A) = (sk_C))) & 
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((((sk_A) = (sk_C))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (~ (((sk_A) = (sk_C))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('25', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((k2_tarski @ X5 @ X6)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf(t45_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.51       ( r2_hidden @ A @ B ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X32 : $i, X33 : $i]:
% 0.21/0.51         ((r2_hidden @ X32 @ X33)
% 0.21/0.51          | ~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X32) @ X33) @ X33))),
% 0.21/0.51      inference('cnf', [status(esa)], [t45_zfmisc_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.21/0.51          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.51          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('31', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.51  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((r2_hidden @ sk_B @ sk_D)
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.21/0.51          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((![X0 : $i, X1 : $i]:
% 0.21/0.51          (~ (r2_hidden @ X1 @ X0)
% 0.21/0.51           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.21/0.51         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D)))
% 0.21/0.51         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '36'])).
% 0.21/0.51  thf('38', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) & 
% 0.21/0.51             (((sk_A) = (sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (~ (((sk_A) = (sk_C))) | 
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.21/0.51       ((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['33'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((r2_hidden @ X12 @ X13)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((r2_hidden @ sk_B @ sk_D))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.21/0.51       ((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['1', '23', '24', '41', '42', '47'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
