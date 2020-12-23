%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xeGXW6jROL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 111 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  435 ( 854 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ( r1_ordinal1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_ordinal1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('24',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','26'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('29',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('33',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t22_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 )
      | ~ ( v1_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_ordinal1 @ sk_A )
        | ~ ( v3_ordinal1 @ X0 )
        | ( r2_hidden @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 )
        | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('41',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ X0 )
        | ( r2_hidden @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xeGXW6jROL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 215 iterations in 0.083s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.53  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.53  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.53  thf(t34_ordinal1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.53           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.53             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.53              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.53                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.53        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.53       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X7)
% 0.20/0.53          | ~ (v3_ordinal1 @ X8)
% 0.20/0.53          | (r1_ordinal1 @ X7 @ X8)
% 0.20/0.53          | (r1_ordinal1 @ X8 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.53       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X10)
% 0.20/0.53          | ~ (v3_ordinal1 @ X11)
% 0.20/0.53          | (r1_tarski @ X10 @ X11)
% 0.20/0.53          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X0)
% 0.20/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.53          | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X0)
% 0.20/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.53          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ X0 @ sk_A)
% 0.20/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_B @ sk_A)))
% 0.20/0.53         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf(t13_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.53       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((X14) = (X13))
% 0.20/0.53          | (r2_hidden @ X14 @ X13)
% 0.20/0.53          | ~ (r2_hidden @ X14 @ (k1_ordinal1 @ X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((sk_A) = (sk_B)))
% 0.20/0.53         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.53             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.20/0.53         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.53             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('24', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf(t29_ordinal1, axiom,
% 0.20/0.53    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X21 : $i]:
% 0.20/0.53         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.53  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.53  thf('30', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_ordinal1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X10)
% 0.20/0.53          | ~ (v3_ordinal1 @ X11)
% 0.20/0.53          | (r1_tarski @ X10 @ X11)
% 0.20/0.53          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.53         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.53         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.53  thf(t22_ordinal1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( v3_ordinal1 @ C ) =>
% 0.20/0.53               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.20/0.53                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (v3_ordinal1 @ X16)
% 0.20/0.53          | ~ (r1_tarski @ X17 @ X16)
% 0.20/0.53          | ~ (r2_hidden @ X16 @ X18)
% 0.20/0.53          | (r2_hidden @ X17 @ X18)
% 0.20/0.53          | ~ (v3_ordinal1 @ X18)
% 0.20/0.53          | ~ (v1_ordinal1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (v1_ordinal1 @ sk_A)
% 0.20/0.53           | ~ (v3_ordinal1 @ X0)
% 0.20/0.53           | (r2_hidden @ sk_A @ X0)
% 0.20/0.53           | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.53           | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_ordinal1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.53  thf('40', plain, (![X6 : $i]: ((v1_ordinal1 @ X6) | ~ (v3_ordinal1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.53  thf('41', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (v3_ordinal1 @ X0)
% 0.20/0.53           | (r2_hidden @ sk_A @ X0)
% 0.20/0.53           | ~ (r2_hidden @ sk_B @ X0)))
% 0.20/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))
% 0.20/0.53         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B))))
% 0.20/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((~ (v3_ordinal1 @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.20/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '44'])).
% 0.20/0.53  thf('46', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '49'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
