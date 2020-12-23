%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RA0LCgptMm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:04 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  500 ( 899 expanded)
%              Number of equality atoms :   53 ( 114 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X69: $i,X70: $i] :
      ( ( r2_hidden @ X69 @ X70 )
      | ~ ( r1_tarski @ ( k1_tarski @ X69 ) @ X70 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X8 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('37',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( sk_A
     != ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( sk_A
     != ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( sk_A
     != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( sk_A
     != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('51',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','49','50'])).

thf('52',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['7','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RA0LCgptMm
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 539 iterations in 0.213s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(t66_zfmisc_1, conjecture,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.53/0.71          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i]:
% 0.53/0.71        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.53/0.71             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(l32_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X12 : $i, X13 : $i]:
% 0.53/0.71         ((r1_tarski @ X12 @ X13)
% 0.53/0.71          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.53/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.71        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.71  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.53/0.71      inference('simplify', [status(thm)], ['2'])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X9 : $i, X11 : $i]:
% 0.53/0.71         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.53/0.71        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.71  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.53/0.71      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.53/0.71  thf('8', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.53/0.71      inference('simplify', [status(thm)], ['2'])).
% 0.53/0.71  thf(t28_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i]:
% 0.53/0.71         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.53/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.71  thf('10', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.71  thf(t100_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X17 @ X18)
% 0.53/0.71           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.53/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.53/0.71      inference('sup+', [status(thm)], ['10', '13'])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('16', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.53/0.71      inference('simplify', [status(thm)], ['15'])).
% 0.53/0.71  thf(l1_zfmisc_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      (![X69 : $i, X70 : $i]:
% 0.53/0.71         ((r2_hidden @ X69 @ X70) | ~ (r1_tarski @ (k1_tarski @ X69) @ X70))),
% 0.53/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.53/0.71  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.71  thf(t1_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.53/0.71       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.53/0.71         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 0.53/0.71          | (r2_hidden @ X5 @ X8)
% 0.53/0.71          | ~ (r2_hidden @ X5 @ X6))),
% 0.53/0.71      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((r2_hidden @ X0 @ X1)
% 0.53/0.71          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (((r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.53/0.71        | (r2_hidden @ sk_B @ sk_A))),
% 0.53/0.71      inference('sup+', [status(thm)], ['14', '20'])).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X69 : $i, X71 : $i]:
% 0.53/0.71         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 0.53/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      (((r2_hidden @ sk_B @ sk_A)
% 0.53/0.71        | (r1_tarski @ (k1_tarski @ sk_B) @ 
% 0.53/0.71           (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i]:
% 0.53/0.71         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.53/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      (((r2_hidden @ sk_B @ sk_A)
% 0.53/0.71        | ((k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.53/0.71            (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)) = (k1_tarski @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.71  thf('26', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.53/0.71      inference('simplify', [status(thm)], ['15'])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i]:
% 0.53/0.71         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.53/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.71  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.71  thf(t49_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.53/0.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.53/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.53/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.53/0.71  thf('30', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.53/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.53/0.71      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      (((r2_hidden @ sk_B @ sk_A)
% 0.53/0.71        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tarski @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['25', '30'])).
% 0.53/0.71  thf('32', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.53/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.53/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.53/0.71           = (k4_xboole_0 @ sk_A @ X0))),
% 0.53/0.71      inference('sup+', [status(thm)], ['32', '33'])).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.53/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.53/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.53/0.71  thf('36', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.53/0.71      inference('simplify', [status(thm)], ['15'])).
% 0.53/0.71  thf('37', plain,
% 0.53/0.71      (![X12 : $i, X14 : $i]:
% 0.53/0.71         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.53/0.71          | ~ (r1_tarski @ X12 @ X14))),
% 0.53/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.71  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.71  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('40', plain, (![X0 : $i]: ((sk_A) != (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.71  thf('41', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((sk_A)
% 0.53/0.71           != (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['35', '40'])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((sk_A)
% 0.53/0.71           != (k3_xboole_0 @ sk_A @ 
% 0.53/0.71               (k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ 
% 0.53/0.71                (k4_xboole_0 @ sk_A @ X0))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['34', '41'])).
% 0.53/0.71  thf('43', plain,
% 0.53/0.71      ((((sk_A)
% 0.53/0.71          != (k3_xboole_0 @ sk_A @ 
% 0.53/0.71              (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k4_xboole_0 @ sk_A @ sk_A))))
% 0.53/0.71        | (r2_hidden @ sk_B @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['31', '42'])).
% 0.53/0.71  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.71  thf(t2_boole, axiom,
% 0.53/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X17 @ X18)
% 0.53/0.71           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.71  thf('47', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.53/0.71  thf(t5_boole, axiom,
% 0.53/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.71  thf('48', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.53/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.71  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.71      inference('sup+', [status(thm)], ['47', '48'])).
% 0.53/0.71  thf('50', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('51', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['43', '44', '49', '50'])).
% 0.53/0.71  thf('52', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.53/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.53/0.71  thf('53', plain,
% 0.53/0.71      (![X69 : $i, X71 : $i]:
% 0.53/0.71         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 0.53/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.53/0.71  thf('54', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.53/0.71      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.71  thf('55', plain, ($false), inference('demod', [status(thm)], ['7', '54'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
