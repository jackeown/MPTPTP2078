%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g81LsZtypE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 239 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  666 (3150 expanded)
%              Number of equality atoms :   85 ( 369 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t70_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ( ( r2_hidden @ B @ C )
            | ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X3 ) @ X2 )
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('7',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_A != sk_B )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X3 )
      | ( r2_hidden @ X3 @ X2 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X3 ) @ X2 )
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_B @ sk_C )
      | ( sk_A = sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_B @ sk_C )
      & ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_A != sk_B )
      & ~ ( r2_hidden @ sk_B @ sk_C )
      & ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ~ ( r2_hidden @ sk_A @ sk_C )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( sk_A = sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X3 ) @ X4 )
        = ( k1_tarski @ X1 ) )
      | ( X1 != X3 )
      | ( r2_hidden @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X3 @ X3 ) @ X4 )
        = ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['14'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('44',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['42','16','17','9','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A = sk_B ) ),
    inference(simpl_trail,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(demod,[status(thm)],['31','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['15','16','17','9','26','48','49'])).

thf('51',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['13','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X3 ) @ X4 )
        = ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['42','16','17','9','43'])).

thf('56',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['11','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g81LsZtypE
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 54 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(t70_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.47         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47          ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.47            ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t70_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.47        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47            = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.21/0.47        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.47        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47            != (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(l38_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.47         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.47          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X3) @ X2) != (k1_tarski @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.47         | ~ (r2_hidden @ sk_A @ sk_C)))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_A @ sk_C))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.47       ~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.47  thf('10', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.21/0.47  thf('11', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((sk_A) = (sk_B))
% 0.21/0.47        | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.47        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47            = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((sk_A) != (sk_B))
% 0.21/0.47        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.47        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47            != (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       ~ (((sk_A) = (sk_B))) | ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('split', [status(esa)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       ~ ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((X1) = (X3))
% 0.21/0.47          | (r2_hidden @ X3 @ X2)
% 0.21/0.47          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X3) @ X2) != (k1_tarski @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.47         | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.47         | ((sk_A) = (sk_B))))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_C)))
% 0.21/0.47         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((sk_A) = (sk_B)))
% 0.21/0.47         <= (~ ((r2_hidden @ sk_B @ sk_C)) & 
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['14'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((sk_B) != (sk_B)))
% 0.21/0.47         <= (~ (((sk_A) = (sk_B))) & 
% 0.21/0.47             ~ ((r2_hidden @ sk_B @ sk_C)) & 
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       ((r2_hidden @ sk_B @ sk_C)) | (((sk_A) = (sk_B)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.47  thf('27', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['12'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_B @ sk_C))
% 0.21/0.47         <= (~ ((r2_hidden @ sk_A @ sk_C)) & (((sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.21/0.47  thf('31', plain, ((~ (r2_hidden @ sk_B @ sk_C)) <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('32', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k2_tarski @ X1 @ X3) @ X4) = (k1_tarski @ X1))
% 0.21/0.47          | ((X1) != (X3))
% 0.21/0.47          | (r2_hidden @ X1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ X4)
% 0.21/0.47          | ((k4_xboole_0 @ (k2_tarski @ X3 @ X3) @ X4) = (k1_tarski @ X3)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.21/0.47          | (r2_hidden @ X0 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['32', '34'])).
% 0.21/0.47  thf('36', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['12'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))) & 
% 0.21/0.47             (((sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf('40', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['12'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))) & 
% 0.21/0.47             (((sk_A) = (sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.47       ~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('split', [status(esa)], ['14'])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.47       ~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.47       (((sk_A) = (sk_B)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['42', '16', '17', '9', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_B)))
% 0.21/0.47         <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['41', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_C)))
% 0.21/0.47         <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '45'])).
% 0.21/0.47  thf('47', plain, (((r2_hidden @ sk_B @ sk_C)) <= ((((sk_A) = (sk_B))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.47  thf('48', plain, (~ (((sk_A) = (sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (((r2_hidden @ sk_B @ sk_C)) | (((sk_A) = (sk_B))) | 
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['12'])).
% 0.21/0.47  thf('50', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)],
% 0.21/0.47                ['15', '16', '17', '9', '26', '48', '49'])).
% 0.21/0.47  thf('51', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['13', '50'])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k2_tarski @ X1 @ X3) @ X4) = (k1_tarski @ X1))
% 0.21/0.47          | ~ (r2_hidden @ X3 @ X4)
% 0.21/0.47          | (r2_hidden @ X1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ sk_C)
% 0.21/0.47          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C) = (k1_tarski @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47                = (k1_tarski @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['42', '16', '17', '9', '43'])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['53', '56'])).
% 0.21/0.47  thf('58', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.47  thf('59', plain, ($false), inference('demod', [status(thm)], ['11', '58'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
