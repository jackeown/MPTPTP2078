%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YiNisXzuuU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  434 ( 869 expanded)
%              Number of equality atoms :   35 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ X31 )
        = X31 )
      | ~ ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('14',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('22',plain,
    ( ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t62_xboole_1,axiom,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X13: $i] :
      ~ ( r2_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['11','27','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','28','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ~ ( r2_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YiNisXzuuU
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 153 iterations in 0.092s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(t68_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54       ( r2_hidden @ A @ B ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54          ( r2_hidden @ A @ B ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(d1_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         (((X17) != (X16))
% 0.20/0.54          | (r2_hidden @ X17 @ X18)
% 0.20/0.54          | ((X18) != (k1_tarski @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.54  thf('3', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf(d5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | (r2_hidden @ X0 @ X3)
% 0.20/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ k1_xboole_0))
% 0.20/0.54         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.20/0.54             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.54       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(l22_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.54       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i]:
% 0.20/0.54         (((k2_xboole_0 @ (k1_tarski @ X32) @ X31) = (X31))
% 0.20/0.54          | ~ (r2_hidden @ X32 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.20/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf(t7_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(t1_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('17', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf(t43_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.20/0.54          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.54          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0))
% 0.20/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.54  thf(d8_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.54       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X6 : $i, X8 : $i]:
% 0.20/0.54         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))
% 0.20/0.54         | (r2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.20/0.54            k1_xboole_0)))
% 0.20/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf(t62_xboole_1, axiom, (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.20/0.54  thf('23', plain, (![X13 : $i]: ~ (r2_xboole_0 @ X13 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.20/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.54         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.20/0.54             ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.54  thf('28', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['11', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.54       ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['11', '27', '29'])).
% 0.20/0.54  thf('31', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['10', '28', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.20/0.54          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X6 : $i, X8 : $i]:
% 0.20/0.54         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k4_xboole_0 @ X1 @ X1) = (X0))
% 0.20/0.54          | (r2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain, (![X13 : $i]: ~ (r2_xboole_0 @ X13 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.20/0.54  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.54          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '40'])).
% 0.20/0.54  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.54      inference('condensation', [status(thm)], ['41'])).
% 0.20/0.54  thf('43', plain, ($false), inference('sup-', [status(thm)], ['31', '42'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
