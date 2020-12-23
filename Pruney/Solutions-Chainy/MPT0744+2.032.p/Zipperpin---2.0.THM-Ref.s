%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCJx1kn37d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 114 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  452 ( 872 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_ordinal1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('5',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('10',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('13',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ( r1_ordinal1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

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
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('36',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_xboole_0 @ X17 @ X16 )
      | ~ ( v1_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('38',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('41',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('45',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('50',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('51',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCJx1kn37d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 118 iterations in 0.065s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.53  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.53  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.53  thf(t34_ordinal1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.53           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.53             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.53              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.53                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.53        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.53       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.53        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf(t13_ordinal1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((X14) = (X13))
% 0.21/0.53          | (r2_hidden @ X14 @ X13)
% 0.21/0.53          | ~ (r2_hidden @ X14 @ (k1_ordinal1 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(d2_ordinal1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.53       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.53          | (r1_tarski @ X7 @ X8)
% 0.21/0.53          | ~ (v1_ordinal1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1))
% 0.21/0.53         | ~ (v1_ordinal1 @ sk_B_1)
% 0.21/0.53         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_ordinal1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.53  thf('9', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.53  thf('10', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.53       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (v3_ordinal1 @ X10)
% 0.21/0.53          | ~ (v3_ordinal1 @ X11)
% 0.21/0.53          | (r1_ordinal1 @ X10 @ X11)
% 0.21/0.53          | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1))
% 0.21/0.53         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.53         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.53         | ~ (v3_ordinal1 @ sk_A)))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.21/0.53         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((sk_A) = (sk_B_1)))
% 0.21/0.53         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.21/0.53             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.21/0.53         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.21/0.53             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(connectedness_r1_ordinal1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.53       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (v3_ordinal1 @ X4)
% 0.21/0.53          | ~ (v3_ordinal1 @ X5)
% 0.21/0.53          | (r1_ordinal1 @ X4 @ X5)
% 0.21/0.53          | (r1_ordinal1 @ X5 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_ordinal1 @ X0 @ sk_A)
% 0.21/0.53          | (r1_ordinal1 @ sk_A @ X0)
% 0.21/0.53          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.21/0.53      inference('eq_fact', [status(thm)], ['23'])).
% 0.21/0.53  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.53       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.53       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (v3_ordinal1 @ X10)
% 0.21/0.53          | ~ (v3_ordinal1 @ X11)
% 0.21/0.53          | (r1_tarski @ X10 @ X11)
% 0.21/0.53          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.21/0.53         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.53         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.53  thf(d8_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.53       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 0.21/0.53         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf(t21_ordinal1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.53           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (v3_ordinal1 @ X16)
% 0.21/0.53          | (r2_hidden @ X17 @ X16)
% 0.21/0.53          | ~ (r2_xboole_0 @ X17 @ X16)
% 0.21/0.53          | ~ (v1_ordinal1 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((((sk_A) = (sk_B_1))
% 0.21/0.53         | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.53         | (r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.53         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.53  thf('41', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.21/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         ((r2_hidden @ X14 @ (k1_ordinal1 @ X15)) | ~ (r2_hidden @ X14 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))
% 0.21/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((((sk_A) = (sk_B_1)))
% 0.21/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.54             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.21/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.54             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.54  thf('50', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_ordinal1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.54       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain, ($false),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '51'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
