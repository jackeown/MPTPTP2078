%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bkEdXyFr4N

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:06 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  447 ( 949 expanded)
%              Number of equality atoms :   21 (  96 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X37 ) )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['13','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X37 ) )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X37 ) )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['31','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bkEdXyFr4N
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.39/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.64  % Solved by: fo/fo7.sh
% 1.39/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.64  % done 3125 iterations in 1.183s
% 1.39/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.64  % SZS output start Refutation
% 1.39/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.39/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.39/1.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.39/1.64  thf(sk_B_type, type, sk_B: $i > $i).
% 1.39/1.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.39/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.39/1.64  thf(d1_xboole_0, axiom,
% 1.39/1.64    (![A:$i]:
% 1.39/1.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.39/1.64  thf('0', plain,
% 1.39/1.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.39/1.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.39/1.64  thf('1', plain,
% 1.39/1.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.39/1.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.39/1.64  thf(l54_zfmisc_1, axiom,
% 1.39/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.39/1.64     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.39/1.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.39/1.64  thf('2', plain,
% 1.39/1.64      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 1.39/1.64         ((r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X37))
% 1.39/1.64          | ~ (r2_hidden @ X35 @ X37)
% 1.39/1.64          | ~ (r2_hidden @ X33 @ X34))),
% 1.39/1.64      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.39/1.64  thf('3', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.64         ((v1_xboole_0 @ X0)
% 1.39/1.64          | ~ (r2_hidden @ X2 @ X1)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X1 @ X0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.64  thf('4', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((v1_xboole_0 @ X0)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X0 @ X1))
% 1.39/1.64          | (v1_xboole_0 @ X1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['0', '3'])).
% 1.39/1.64  thf(t114_zfmisc_1, conjecture,
% 1.39/1.64    (![A:$i,B:$i]:
% 1.39/1.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 1.39/1.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.64         ( ( A ) = ( B ) ) ) ))).
% 1.39/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.64    (~( ![A:$i,B:$i]:
% 1.39/1.64        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 1.39/1.64          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.64            ( ( A ) = ( B ) ) ) ) )),
% 1.39/1.64    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 1.39/1.64  thf('5', plain,
% 1.39/1.64      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('6', plain,
% 1.39/1.64      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.39/1.64         ((r2_hidden @ X35 @ X36)
% 1.39/1.64          | ~ (r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X36)))),
% 1.39/1.64      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.39/1.64  thf('7', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.39/1.64          | (r2_hidden @ X0 @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['5', '6'])).
% 1.39/1.64  thf('8', plain,
% 1.39/1.64      (((v1_xboole_0 @ sk_B_1)
% 1.39/1.64        | (v1_xboole_0 @ sk_A)
% 1.39/1.64        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['4', '7'])).
% 1.39/1.64  thf(l13_xboole_0, axiom,
% 1.39/1.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.39/1.64  thf('9', plain,
% 1.39/1.64      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.39/1.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.39/1.64  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('11', plain, (![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.39/1.64      inference('sup-', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('12', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.39/1.64      inference('simplify', [status(thm)], ['11'])).
% 1.39/1.64  thf('13', plain,
% 1.39/1.64      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 1.39/1.64      inference('clc', [status(thm)], ['8', '12'])).
% 1.39/1.64  thf('14', plain,
% 1.39/1.64      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.39/1.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.39/1.64  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('16', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.39/1.64      inference('sup-', [status(thm)], ['14', '15'])).
% 1.39/1.64  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.39/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.39/1.64  thf('18', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 1.39/1.64      inference('clc', [status(thm)], ['13', '17'])).
% 1.39/1.64  thf(d3_tarski, axiom,
% 1.39/1.64    (![A:$i,B:$i]:
% 1.39/1.64     ( ( r1_tarski @ A @ B ) <=>
% 1.39/1.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.39/1.64  thf('19', plain,
% 1.39/1.64      (![X4 : $i, X6 : $i]:
% 1.39/1.64         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.39/1.64      inference('cnf', [status(esa)], [d3_tarski])).
% 1.39/1.64  thf('20', plain,
% 1.39/1.64      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 1.39/1.64         ((r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X37))
% 1.39/1.64          | ~ (r2_hidden @ X35 @ X37)
% 1.39/1.64          | ~ (r2_hidden @ X33 @ X34))),
% 1.39/1.64      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.39/1.64  thf('21', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.39/1.64         ((r1_tarski @ X0 @ X1)
% 1.39/1.64          | ~ (r2_hidden @ X3 @ X2)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X2 @ X0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['19', '20'])).
% 1.39/1.64  thf('22', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_C @ X1 @ X0)) @ 
% 1.39/1.64           (k2_zfmisc_1 @ sk_A @ X0))
% 1.39/1.64          | (r1_tarski @ X0 @ X1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['18', '21'])).
% 1.39/1.64  thf('23', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.39/1.64          | (r2_hidden @ X0 @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['5', '6'])).
% 1.39/1.64  thf('24', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.39/1.64  thf('25', plain,
% 1.39/1.64      (![X4 : $i, X6 : $i]:
% 1.39/1.64         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.39/1.64      inference('cnf', [status(esa)], [d3_tarski])).
% 1.39/1.64  thf('26', plain,
% 1.39/1.64      (((r1_tarski @ sk_B_1 @ sk_A) | (r1_tarski @ sk_B_1 @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['24', '25'])).
% 1.39/1.64  thf('27', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.39/1.64      inference('simplify', [status(thm)], ['26'])).
% 1.39/1.64  thf(d10_xboole_0, axiom,
% 1.39/1.64    (![A:$i,B:$i]:
% 1.39/1.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.39/1.64  thf('28', plain,
% 1.39/1.64      (![X12 : $i, X14 : $i]:
% 1.39/1.64         (((X12) = (X14))
% 1.39/1.64          | ~ (r1_tarski @ X14 @ X12)
% 1.39/1.64          | ~ (r1_tarski @ X12 @ X14))),
% 1.39/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.39/1.64  thf('29', plain, ((~ (r1_tarski @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['27', '28'])).
% 1.39/1.64  thf('30', plain, (((sk_A) != (sk_B_1))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('31', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 1.39/1.64      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 1.39/1.64  thf('32', plain,
% 1.39/1.64      (![X4 : $i, X6 : $i]:
% 1.39/1.64         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.39/1.64      inference('cnf', [status(esa)], [d3_tarski])).
% 1.39/1.64  thf('33', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((v1_xboole_0 @ X0)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X0 @ X1))
% 1.39/1.64          | (v1_xboole_0 @ X1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['0', '3'])).
% 1.39/1.64  thf('34', plain,
% 1.39/1.64      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('35', plain,
% 1.39/1.64      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.39/1.64         ((r2_hidden @ X33 @ X34)
% 1.39/1.64          | ~ (r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X36)))),
% 1.39/1.64      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.39/1.64  thf('36', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.39/1.64          | (r2_hidden @ X1 @ sk_B_1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['34', '35'])).
% 1.39/1.64  thf('37', plain,
% 1.39/1.64      (((v1_xboole_0 @ sk_B_1)
% 1.39/1.64        | (v1_xboole_0 @ sk_A)
% 1.39/1.64        | (r2_hidden @ (sk_B @ sk_A) @ sk_B_1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['33', '36'])).
% 1.39/1.64  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.39/1.64      inference('simplify', [status(thm)], ['11'])).
% 1.39/1.64  thf('39', plain,
% 1.39/1.64      (((r2_hidden @ (sk_B @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 1.39/1.64      inference('clc', [status(thm)], ['37', '38'])).
% 1.39/1.64  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.39/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.39/1.64  thf('41', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_1)),
% 1.39/1.64      inference('clc', [status(thm)], ['39', '40'])).
% 1.39/1.64  thf('42', plain,
% 1.39/1.64      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 1.39/1.64         ((r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X37))
% 1.39/1.64          | ~ (r2_hidden @ X35 @ X37)
% 1.39/1.64          | ~ (r2_hidden @ X33 @ X34))),
% 1.39/1.64      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.39/1.64  thf('43', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (r2_hidden @ X1 @ X0)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_A)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['41', '42'])).
% 1.39/1.64  thf('44', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r1_tarski @ X0 @ X1)
% 1.39/1.64          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ sk_A)) @ 
% 1.39/1.64             (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['32', '43'])).
% 1.39/1.64  thf('45', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.39/1.64          | (r2_hidden @ X1 @ sk_B_1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['34', '35'])).
% 1.39/1.64  thf('46', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['44', '45'])).
% 1.39/1.64  thf('47', plain,
% 1.39/1.64      (![X4 : $i, X6 : $i]:
% 1.39/1.64         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.39/1.64      inference('cnf', [status(esa)], [d3_tarski])).
% 1.39/1.64  thf('48', plain,
% 1.39/1.64      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['46', '47'])).
% 1.39/1.64  thf('49', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.39/1.64      inference('simplify', [status(thm)], ['48'])).
% 1.39/1.64  thf('50', plain, ($false), inference('demod', [status(thm)], ['31', '49'])).
% 1.39/1.64  
% 1.39/1.64  % SZS output end Refutation
% 1.39/1.64  
% 1.39/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
