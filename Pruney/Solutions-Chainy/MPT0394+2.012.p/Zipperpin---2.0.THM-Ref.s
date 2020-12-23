%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktJqVu5H0P

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 242 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  454 (1808 expanded)
%              Number of equality atoms :   51 ( 142 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X29 ) @ ( k1_setfam_1 @ X30 ) ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('15',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( ( k3_xboole_0 @ X28 @ ( k1_tarski @ X27 ) )
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('36',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['4','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktJqVu5H0P
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 312 iterations in 0.131s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(t12_setfam_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.58         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t41_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_tarski @ A @ B ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X24 : $i, X25 : $i]:
% 0.40/0.58         ((k2_tarski @ X24 @ X25)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.40/0.58  thf(t11_setfam_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.58  thf('2', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.58  thf(t10_setfam_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.58          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.40/0.58            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X29 : $i, X30 : $i]:
% 0.40/0.58         (((X29) = (k1_xboole_0))
% 0.40/0.58          | ((k1_setfam_1 @ (k2_xboole_0 @ X29 @ X30))
% 0.40/0.58              = (k3_xboole_0 @ (k1_setfam_1 @ X29) @ (k1_setfam_1 @ X30)))
% 0.40/0.58          | ((X30) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.40/0.58            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.40/0.58          | ((X1) = (k1_xboole_0))
% 0.40/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf(t17_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.58  thf('6', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.58  thf(d7_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X6 : $i, X8 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.58  thf(t4_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X10 @ X11)
% 0.40/0.58          | (r2_hidden @ (sk_C @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.58  thf(d4_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.58          | (r2_hidden @ X4 @ X2)
% 0.40/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['10', '12'])).
% 0.40/0.58  thf('14', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.58          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.40/0.58  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 0.40/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X14 : $i, X16 : $i]:
% 0.40/0.58         (((X14) = (X16))
% 0.40/0.58          | ~ (r1_tarski @ X16 @ X14)
% 0.40/0.58          | ~ (r1_tarski @ X14 @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.58          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.40/0.58          | ((X0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '26'])).
% 0.40/0.58  thf(t69_enumset1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(l29_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.40/0.58       ( r2_hidden @ B @ A ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X27 : $i, X28 : $i]:
% 0.40/0.58         ((r2_hidden @ X27 @ X28)
% 0.40/0.58          | ((k3_xboole_0 @ X28 @ (k1_tarski @ X27)) != (k1_tarski @ X27)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (k1_tarski @ X0))
% 0.40/0.58          | (r2_hidden @ X0 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['27', '30'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.58          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '17'])).
% 0.40/0.58  thf('36', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.40/0.58      inference('clc', [status(thm)], ['31', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((X1) = (k1_xboole_0))
% 0.40/0.58          | ((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.40/0.58              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.40/0.58      inference('clc', [status(thm)], ['4', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.40/0.58            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.40/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['1', '38'])).
% 0.40/0.58  thf('40', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.40/0.58      inference('clc', [status(thm)], ['31', '36'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('clc', [status(thm)], ['41', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '43'])).
% 0.40/0.58  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
