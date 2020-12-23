%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1n1EgWH3iJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 213 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  468 (2846 expanded)
%              Number of equality atoms :   99 ( 657 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('19',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('36',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('37',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('40',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('41',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['34','38','39','40'])).

thf('42',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','41'])).

thf('43',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','38','39','47'])).

thf('49',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','42','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1n1EgWH3iJ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:46:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 176 iterations in 0.072s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf(t46_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf(t43_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.20/0.53  thf('6', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i]:
% 0.20/0.53         (((X32) = (k1_tarski @ X31))
% 0.20/0.53          | ((X32) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X32 @ (k1_tarski @ X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((((sk_C_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf(t1_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('26', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.53  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.53  thf('29', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((sk_C_1) != (sk_C_1)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))) & 
% 0.20/0.53             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_tarski @ sk_A))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['30'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((sk_B_1) != (sk_B_1)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.20/0.53             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['30'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('41', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['34', '38', '39', '40'])).
% 0.20/0.53  thf('42', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['13', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['30'])).
% 0.20/0.53  thf('44', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.20/0.53       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('48', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['34', '38', '39', '47'])).
% 0.20/0.53  thf('49', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['45', '48'])).
% 0.20/0.53  thf('50', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['11', '42', '49'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
