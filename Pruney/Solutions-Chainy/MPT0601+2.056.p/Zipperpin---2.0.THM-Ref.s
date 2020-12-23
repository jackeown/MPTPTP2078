%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qkNAATW2rU

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:48 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 105 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  360 ( 877 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k11_relat_1 @ X21 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ ( k11_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','24','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['7','26'])).

thf('28',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('32',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','24'])).

thf('33',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qkNAATW2rU
% 0.17/0.38  % Computer   : n005.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 16:20:48 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 70 iterations in 0.025s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.24/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(t7_xboole_0, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.50  thf(t204_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ C ) =>
% 0.24/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.24/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X20 @ (k11_relat_1 @ X21 @ X22))
% 0.24/0.50          | (r2_hidden @ (k4_tarski @ X22 @ X20) @ X21)
% 0.24/0.50          | ~ (v1_relat_1 @ X21))),
% 0.24/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.24/0.50             X1))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(d4_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.24/0.50       ( ![C:$i]:
% 0.24/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.24/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.50         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.24/0.50          | (r2_hidden @ X13 @ X16)
% 0.24/0.50          | ((X16) != (k1_relat_1 @ X15)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.50         ((r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 0.24/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.24/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X0)
% 0.24/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.24/0.50  thf(t205_relat_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.24/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i]:
% 0.24/0.50        ( ( v1_relat_1 @ B ) =>
% 0.24/0.50          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.24/0.50            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.24/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.24/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.24/0.51      inference('split', [status(esa)], ['6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.24/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.24/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.24/0.51         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.51      inference('split', [status(esa)], ['6'])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.24/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X17 @ X16)
% 0.24/0.51          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.24/0.51          | ((X16) != (k1_relat_1 @ X15)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X15 : $i, X17 : $i]:
% 0.24/0.51         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.24/0.51          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.24/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['11', '13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.51         (~ (r2_hidden @ (k4_tarski @ X22 @ X20) @ X21)
% 0.24/0.51          | (r2_hidden @ X20 @ (k11_relat_1 @ X21 @ X22))
% 0.24/0.51          | ~ (v1_relat_1 @ X21))),
% 0.24/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (((~ (v1_relat_1 @ sk_B_1)
% 0.24/0.51         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.24/0.51            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.24/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.51  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.24/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.24/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.24/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.24/0.51             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['10', '18'])).
% 0.24/0.51  thf(t4_boole, axiom,
% 0.24/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.24/0.51  thf(t64_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.24/0.51       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.51         (((X7) != (X9))
% 0.24/0.51          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9))))),
% 0.24/0.51      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i]:
% 0.24/0.51         ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.24/0.51  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.24/0.51       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['19', '23'])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.24/0.51       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.51      inference('split', [status(esa)], ['6'])).
% 0.24/0.51  thf('26', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['9', '24', '25'])).
% 0.24/0.51  thf('27', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['7', '26'])).
% 0.24/0.51  thf('28', plain,
% 0.24/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.24/0.51        | ~ (v1_relat_1 @ sk_B_1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['5', '27'])).
% 0.24/0.51  thf('29', plain, ((v1_relat_1 @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('30', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.24/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.24/0.51  thf('31', plain,
% 0.24/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.24/0.51         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.51      inference('split', [status(esa)], ['8'])).
% 0.24/0.51  thf('32', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['9', '24'])).
% 0.24/0.51  thf('33', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['31', '32'])).
% 0.24/0.51  thf('34', plain, ($false),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
