%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZ9eNpxJPr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  496 ( 708 expanded)
%              Number of equality atoms :   47 (  69 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(condensation,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZ9eNpxJPr
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.02/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.22  % Solved by: fo/fo7.sh
% 1.02/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.22  % done 684 iterations in 0.766s
% 1.02/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.22  % SZS output start Refutation
% 1.02/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.02/1.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.22  thf(d4_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.02/1.22       ( ![D:$i]:
% 1.02/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.22           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.02/1.22  thf('0', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.22         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf(commutativity_k3_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.02/1.22  thf('1', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf(t2_boole, axiom,
% 1.02/1.22    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.02/1.22  thf('2', plain,
% 1.02/1.22      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.02/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.02/1.22  thf('3', plain,
% 1.02/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.02/1.22      inference('sup+', [status(thm)], ['1', '2'])).
% 1.02/1.22  thf('4', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X6 @ X5)
% 1.02/1.22          | (r2_hidden @ X6 @ X4)
% 1.02/1.22          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('5', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.22         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['4'])).
% 1.02/1.22  thf('6', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['3', '5'])).
% 1.02/1.22  thf('7', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 1.02/1.22          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['0', '6'])).
% 1.02/1.22  thf('8', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('condensation', [status(thm)], ['7'])).
% 1.02/1.22  thf(d1_tarski, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.02/1.22       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.02/1.22  thf('9', plain,
% 1.02/1.22      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X17 @ X16)
% 1.02/1.22          | ((X17) = (X14))
% 1.02/1.22          | ((X16) != (k1_tarski @ X14)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d1_tarski])).
% 1.02/1.22  thf('10', plain,
% 1.02/1.22      (![X14 : $i, X17 : $i]:
% 1.02/1.22         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['9'])).
% 1.02/1.22  thf('11', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.22          | ((sk_D @ k1_xboole_0 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['8', '10'])).
% 1.02/1.22  thf('12', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.22         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('13', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['3', '5'])).
% 1.02/1.22  thf('14', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 1.02/1.22          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.02/1.22  thf('15', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.22      inference('condensation', [status(thm)], ['14'])).
% 1.02/1.22  thf('16', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ X0 @ X1)
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.22          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.02/1.22      inference('sup+', [status(thm)], ['11', '15'])).
% 1.02/1.22  thf('17', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.22          | (r2_hidden @ X0 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['16'])).
% 1.02/1.22  thf('18', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf(d7_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.02/1.22       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.02/1.22  thf('19', plain,
% 1.02/1.22      (![X8 : $i, X10 : $i]:
% 1.02/1.22         ((r1_xboole_0 @ X8 @ X10)
% 1.02/1.22          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.02/1.22  thf('20', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('sup-', [status(thm)], ['18', '19'])).
% 1.02/1.22  thf('21', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.22          | (r2_hidden @ X0 @ X1)
% 1.02/1.22          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.02/1.22      inference('sup-', [status(thm)], ['17', '20'])).
% 1.02/1.22  thf('22', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['21'])).
% 1.02/1.22  thf(t58_zfmisc_1, conjecture,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.02/1.22       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.02/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.22    (~( ![A:$i,B:$i]:
% 1.02/1.22        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.02/1.22          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.02/1.22    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.02/1.22  thf('23', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('24', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.02/1.22      inference('sup-', [status(thm)], ['22', '23'])).
% 1.02/1.22  thf('25', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.22         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.02/1.22          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('26', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.22      inference('eq_fact', [status(thm)], ['25'])).
% 1.02/1.22  thf('27', plain,
% 1.02/1.22      (![X14 : $i, X17 : $i]:
% 1.02/1.22         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['9'])).
% 1.02/1.22  thf('28', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.02/1.22          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.02/1.22  thf('29', plain,
% 1.02/1.22      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.22         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('30', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.22          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 1.02/1.22               (k1_tarski @ X0))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 1.02/1.22               (k1_tarski @ X0))
% 1.02/1.22          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['28', '29'])).
% 1.02/1.22  thf('31', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 1.02/1.22             (k1_tarski @ X0))
% 1.02/1.22          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.02/1.22          | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['30'])).
% 1.02/1.22  thf('32', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.22      inference('eq_fact', [status(thm)], ['25'])).
% 1.02/1.22  thf('33', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.22          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.02/1.22      inference('clc', [status(thm)], ['31', '32'])).
% 1.02/1.22  thf('34', plain,
% 1.02/1.22      (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.02/1.22      inference('sup-', [status(thm)], ['24', '33'])).
% 1.02/1.22  thf('35', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('36', plain,
% 1.02/1.22      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.02/1.22      inference('demod', [status(thm)], ['34', '35'])).
% 1.02/1.22  thf('37', plain,
% 1.02/1.22      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('38', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.22  thf('39', plain,
% 1.02/1.22      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['37', '38'])).
% 1.02/1.22  thf('40', plain, ($false),
% 1.02/1.22      inference('simplify_reflect-', [status(thm)], ['36', '39'])).
% 1.02/1.22  
% 1.02/1.22  % SZS output end Refutation
% 1.02/1.22  
% 1.02/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
