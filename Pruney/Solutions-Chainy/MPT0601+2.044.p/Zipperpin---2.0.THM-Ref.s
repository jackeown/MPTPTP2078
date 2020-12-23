%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K4bsrvFSVN

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 106 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  372 ( 901 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_2 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_2 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k11_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['7','27'])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('33',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','25'])).

thf('34',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K4bsrvFSVN
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 98 iterations in 0.061s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(t7_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.51  thf(t204_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.20/0.51             X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(d4_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.20/0.51          | (r2_hidden @ X10 @ X13)
% 0.20/0.51          | ((X13) != (k1_relat_1 @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.20/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.51  thf(t205_relat_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.51         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ B ) =>
% 0.20/0.51          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.51            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X14 @ X13)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_2 @ X14 @ X12)) @ X12)
% 0.20/0.51          | ((X13) != (k1_relat_1 @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X12 : $i, X14 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_2 @ X14 @ X12)) @ X12)
% 0.20/0.51          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X19 @ X17) @ X18)
% 0.20/0.51          | (r2_hidden @ X17 @ (k11_relat_1 @ X18 @ X19))
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ 
% 0.20/0.51            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.51             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['10', '18'])).
% 0.20/0.51  thf(t4_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.51  thf(d5_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.51          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.51  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('condensation', [status(thm)], ['23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.51       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.51       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('27', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '25', '26'])).
% 0.20/0.51  thf('28', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['7', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '28'])).
% 0.20/0.51  thf('30', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.20/0.51         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('33', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '25'])).
% 0.20/0.51  thf('34', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
