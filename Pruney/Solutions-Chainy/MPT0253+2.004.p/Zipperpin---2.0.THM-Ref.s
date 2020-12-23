%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fzIHkzO43P

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:31 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  515 ( 887 expanded)
%              Number of equality atoms :   51 (  95 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

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
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('53',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fzIHkzO43P
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 363 iterations in 0.158s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(t48_zfmisc_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.38/0.61       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.38/0.61          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.38/0.61  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t38_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.38/0.61         ((r1_tarski @ (k2_tarski @ X40 @ X42) @ X43)
% 0.38/0.61          | ~ (r2_hidden @ X42 @ X43)
% 0.38/0.61          | ~ (r2_hidden @ X40 @ X43))),
% 0.38/0.61      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_A) @ sk_B)),
% 0.38/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.38/0.61  thf(commutativity_k2_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X27 : $i, X28 : $i]:
% 0.38/0.61         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.61  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 0.38/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf(t28_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X22 : $i, X23 : $i]:
% 0.38/0.61         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.38/0.61         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1))
% 0.38/0.61         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf(t100_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X19 @ X20)
% 0.38/0.61           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.38/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 0.38/0.61            (k2_tarski @ sk_A @ sk_C_1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['10', '13'])).
% 0.38/0.61  thf(t2_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.38/0.61       ( ( A ) = ( B ) ) ))).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         (((X15) = (X14))
% 0.38/0.61          | (r2_hidden @ (sk_C @ X14 @ X15) @ X14)
% 0.38/0.61          | (r2_hidden @ (sk_C @ X14 @ X15) @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X27 : $i, X28 : $i]:
% 0.38/0.61         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.61  thf(l51_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X38 : $i, X39 : $i]:
% 0.38/0.61         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.38/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X38 : $i, X39 : $i]:
% 0.38/0.61         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.38/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.61  thf(t1_boole, axiom,
% 0.38/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.61  thf('21', plain, (![X21 : $i]: ((k2_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.61  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf(t39_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.38/0.61           = (k2_xboole_0 @ X25 @ X26))),
% 0.38/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.61  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.61  thf(d5_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.61       ( ![D:$i]:
% 0.38/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X12 @ X11)
% 0.38/0.61          | ~ (r2_hidden @ X12 @ X10)
% 0.38/0.61          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X12 @ X10)
% 0.38/0.61          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['26', '28'])).
% 0.38/0.61  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.61      inference('condensation', [status(thm)], ['29'])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '30'])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('33', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 0.38/0.61      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X22 : $i, X23 : $i]:
% 0.38/0.61         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.61  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X12 @ X11)
% 0.38/0.61          | (r2_hidden @ X12 @ X9)
% 0.38/0.61          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.38/0.61         ((r2_hidden @ X12 @ X9)
% 0.38/0.61          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X12 @ X10)
% 0.38/0.61          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.38/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('clc', [status(thm)], ['40', '43'])).
% 0.38/0.61  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['31', '44'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['14', '45'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.38/0.61           = (k2_xboole_0 @ X25 @ X26))),
% 0.38/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.38/0.61         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['46', '47'])).
% 0.38/0.61  thf('49', plain, (![X21 : $i]: ((k2_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) != (sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.38/0.61  thf('54', plain, ($false),
% 0.38/0.61      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
