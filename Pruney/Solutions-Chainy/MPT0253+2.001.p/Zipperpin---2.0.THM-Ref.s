%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f3DWx8V9ep

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:30 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 114 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  476 ( 795 expanded)
%              Number of equality atoms :   46 (  83 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X47 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r2_hidden @ X47 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X28: $i] :
      ( ( k2_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ( X23 != X24 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X24: $i] :
      ( r1_tarski @ X24 @ X24 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ X15 @ X12 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','41'])).

thf('43',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( k2_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f3DWx8V9ep
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.74  % Solved by: fo/fo7.sh
% 0.50/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.74  % done 666 iterations in 0.279s
% 0.50/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.74  % SZS output start Refutation
% 0.50/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.74  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.50/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(t48_zfmisc_1, conjecture,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.50/0.74       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.50/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.74        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.50/0.74          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.50/0.74    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.50/0.74  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(t38_zfmisc_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.50/0.74       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.50/0.74  thf('2', plain,
% 0.50/0.74      (![X47 : $i, X49 : $i, X50 : $i]:
% 0.50/0.74         ((r1_tarski @ (k2_tarski @ X47 @ X49) @ X50)
% 0.50/0.74          | ~ (r2_hidden @ X49 @ X50)
% 0.50/0.74          | ~ (r2_hidden @ X47 @ X50))),
% 0.50/0.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.50/0.74  thf('3', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.50/0.74          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.74  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_A) @ sk_B_1)),
% 0.50/0.74      inference('sup-', [status(thm)], ['0', '3'])).
% 0.50/0.74  thf(commutativity_k2_tarski, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.50/0.74  thf('5', plain,
% 0.50/0.74      (![X34 : $i, X35 : $i]:
% 0.50/0.74         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 0.50/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.50/0.74  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)),
% 0.50/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.74  thf(t28_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.74  thf('7', plain,
% 0.50/0.74      (![X29 : $i, X30 : $i]:
% 0.50/0.74         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 0.50/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.74  thf('8', plain,
% 0.50/0.74      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 0.50/0.74         = (k2_tarski @ sk_A @ sk_C_2))),
% 0.50/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.74  thf(t100_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.74  thf('9', plain,
% 0.50/0.74      (![X26 : $i, X27 : $i]:
% 0.50/0.74         ((k4_xboole_0 @ X26 @ X27)
% 0.50/0.74           = (k5_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.74  thf('10', plain,
% 0.50/0.74      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 0.50/0.74         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ 
% 0.50/0.74            (k2_tarski @ sk_A @ sk_C_2)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf(t2_tarski, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.50/0.74       ( ( A ) = ( B ) ) ))).
% 0.50/0.74  thf('11', plain,
% 0.50/0.74      (![X17 : $i, X18 : $i]:
% 0.50/0.74         (((X18) = (X17))
% 0.50/0.74          | (r2_hidden @ (sk_C @ X17 @ X18) @ X17)
% 0.50/0.74          | (r2_hidden @ (sk_C @ X17 @ X18) @ X18))),
% 0.50/0.74      inference('cnf', [status(esa)], [t2_tarski])).
% 0.50/0.74  thf('12', plain,
% 0.50/0.74      (![X34 : $i, X35 : $i]:
% 0.50/0.74         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 0.50/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.50/0.74  thf(l51_zfmisc_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.74  thf('13', plain,
% 0.50/0.74      (![X45 : $i, X46 : $i]:
% 0.50/0.74         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.50/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.74  thf('14', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.74  thf('15', plain,
% 0.50/0.74      (![X45 : $i, X46 : $i]:
% 0.50/0.74         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.50/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.74  thf('16', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.74  thf(t1_boole, axiom,
% 0.50/0.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.74  thf('17', plain, (![X28 : $i]: ((k2_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.50/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.74  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.50/0.74  thf(t39_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.74  thf('19', plain,
% 0.50/0.74      (![X32 : $i, X33 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32))
% 0.50/0.74           = (k2_xboole_0 @ X32 @ X33))),
% 0.50/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.74  thf('20', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.74  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.50/0.74  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.50/0.74  thf(d5_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.50/0.74       ( ![D:$i]:
% 0.50/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X15 @ X14)
% 0.50/0.74          | ~ (r2_hidden @ X15 @ X13)
% 0.50/0.74          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 0.50/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.50/0.74  thf('24', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X15 @ X13)
% 0.50/0.74          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['22', '24'])).
% 0.50/0.74  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.74      inference('condensation', [status(thm)], ['25'])).
% 0.50/0.74  thf('27', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['11', '26'])).
% 0.50/0.74  thf(d10_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.74  thf('28', plain,
% 0.50/0.74      (![X23 : $i, X24 : $i]: ((r1_tarski @ X23 @ X24) | ((X23) != (X24)))),
% 0.50/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.74  thf('29', plain, (![X24 : $i]: (r1_tarski @ X24 @ X24)),
% 0.50/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      (![X29 : $i, X30 : $i]:
% 0.50/0.74         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 0.50/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.74  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.74  thf('32', plain,
% 0.50/0.74      (![X26 : $i, X27 : $i]:
% 0.50/0.74         ((k4_xboole_0 @ X26 @ X27)
% 0.50/0.74           = (k5_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.74  thf('33', plain,
% 0.50/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.50/0.74  thf('34', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X15 @ X14)
% 0.50/0.74          | (r2_hidden @ X15 @ X12)
% 0.50/0.74          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 0.50/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.50/0.74  thf('35', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.50/0.74         ((r2_hidden @ X15 @ X12)
% 0.50/0.74          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['34'])).
% 0.50/0.74  thf('36', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['33', '35'])).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X15 @ X13)
% 0.50/0.74          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.74  thf('39', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.50/0.74          | ~ (r2_hidden @ X1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.74  thf('40', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('clc', [status(thm)], ['36', '39'])).
% 0.50/0.74  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['27', '40'])).
% 0.50/0.74  thf('42', plain,
% 0.50/0.74      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) = (k1_xboole_0))),
% 0.50/0.74      inference('demod', [status(thm)], ['10', '41'])).
% 0.50/0.74  thf('43', plain,
% 0.50/0.74      (![X32 : $i, X33 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32))
% 0.50/0.74           = (k2_xboole_0 @ X32 @ X33))),
% 0.50/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.74  thf('44', plain,
% 0.50/0.74      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.50/0.74         = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.74  thf('45', plain, (![X28 : $i]: ((k2_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.50/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.74  thf('46', plain,
% 0.50/0.74      (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 0.50/0.74      inference('demod', [status(thm)], ['44', '45'])).
% 0.50/0.74  thf('47', plain,
% 0.50/0.74      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) != (sk_B_1))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('48', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.74  thf('49', plain,
% 0.50/0.74      (((k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)) != (sk_B_1))),
% 0.50/0.74      inference('demod', [status(thm)], ['47', '48'])).
% 0.50/0.74  thf('50', plain, ($false),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.59/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
