%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NP4kYQV4y

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:33 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   75 (  92 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  565 ( 790 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

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

thf('34',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NP4kYQV4y
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:22:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.38/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.62  % Solved by: fo/fo7.sh
% 1.38/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.62  % done 2226 iterations in 1.165s
% 1.38/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.62  % SZS output start Refutation
% 1.38/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.38/1.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.38/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.38/1.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.62  thf(l27_zfmisc_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.38/1.62  thf('0', plain,
% 1.38/1.62      (![X32 : $i, X33 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 1.38/1.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.38/1.62  thf(d7_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.38/1.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.38/1.62  thf('1', plain,
% 1.38/1.62      (![X14 : $i, X15 : $i]:
% 1.38/1.62         (((k3_xboole_0 @ X14 @ X15) = (k1_xboole_0))
% 1.38/1.62          | ~ (r1_xboole_0 @ X14 @ X15))),
% 1.38/1.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.38/1.62  thf('2', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r2_hidden @ X1 @ X0)
% 1.38/1.62          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['0', '1'])).
% 1.38/1.62  thf(t47_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('3', plain,
% 1.38/1.62      (![X22 : $i, X23 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 1.38/1.62           = (k4_xboole_0 @ X22 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.38/1.62  thf(t48_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('4', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.38/1.62           = (k3_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('5', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.38/1.62           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['3', '4'])).
% 1.38/1.62  thf('6', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.38/1.62           = (k3_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('7', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_xboole_0 @ X1 @ X0)
% 1.38/1.62           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['5', '6'])).
% 1.38/1.62  thf('8', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 1.38/1.62          | (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['2', '7'])).
% 1.38/1.62  thf(t3_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.38/1.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.38/1.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.38/1.62  thf('9', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X18))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('10', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X17))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf(d5_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.38/1.62       ( ![D:$i]:
% 1.38/1.62         ( ( r2_hidden @ D @ C ) <=>
% 1.38/1.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.38/1.62  thf('11', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X12 @ X11)
% 1.38/1.62          | ~ (r2_hidden @ X12 @ X10)
% 1.38/1.62          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.62  thf('12', plain,
% 1.38/1.62      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X12 @ X10)
% 1.38/1.62          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['11'])).
% 1.38/1.62  thf('13', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.38/1.62          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['10', '12'])).
% 1.38/1.62  thf('14', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.38/1.62          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['9', '13'])).
% 1.38/1.62  thf('15', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.38/1.62      inference('simplify', [status(thm)], ['14'])).
% 1.38/1.62  thf('16', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X17))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('17', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X18))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('18', plain,
% 1.38/1.62      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X19 @ X17)
% 1.38/1.62          | ~ (r2_hidden @ X19 @ X20)
% 1.38/1.62          | ~ (r1_xboole_0 @ X17 @ X20))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('19', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X1 @ X0)
% 1.38/1.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.38/1.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.38/1.62      inference('sup-', [status(thm)], ['17', '18'])).
% 1.38/1.62  thf('20', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X0 @ X1)
% 1.38/1.62          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.38/1.62          | (r1_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['16', '19'])).
% 1.38/1.62  thf('21', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('simplify', [status(thm)], ['20'])).
% 1.38/1.62  thf('22', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['15', '21'])).
% 1.38/1.62  thf('23', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X18))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf(d4_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.38/1.62       ( ![D:$i]:
% 1.38/1.62         ( ( r2_hidden @ D @ C ) <=>
% 1.38/1.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.38/1.62  thf('24', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X6 @ X5)
% 1.38/1.62          | (r2_hidden @ X6 @ X4)
% 1.38/1.62          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.38/1.62  thf('25', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.38/1.62         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['24'])).
% 1.38/1.62  thf('26', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.62          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['23', '25'])).
% 1.38/1.62  thf('27', plain,
% 1.38/1.62      (![X17 : $i, X18 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X17 @ X18) | (r2_hidden @ (sk_C @ X18 @ X17) @ X17))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('28', plain,
% 1.38/1.62      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X19 @ X17)
% 1.38/1.62          | ~ (r2_hidden @ X19 @ X20)
% 1.38/1.62          | ~ (r1_xboole_0 @ X17 @ X20))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('29', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X0 @ X1)
% 1.38/1.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.38/1.62          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.38/1.62      inference('sup-', [status(thm)], ['27', '28'])).
% 1.38/1.62  thf('30', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 1.38/1.62          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.38/1.62          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['26', '29'])).
% 1.38/1.62  thf('31', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         (~ (r1_xboole_0 @ X1 @ X0)
% 1.38/1.62          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['30'])).
% 1.38/1.62  thf('32', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['22', '31'])).
% 1.38/1.62  thf('33', plain,
% 1.38/1.62      (![X32 : $i, X33 : $i]:
% 1.38/1.62         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 1.38/1.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.38/1.62  thf(t58_zfmisc_1, conjecture,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.38/1.62       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.38/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.62    (~( ![A:$i,B:$i]:
% 1.38/1.62        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.38/1.62          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.38/1.62    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.38/1.62  thf('34', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('35', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.38/1.62  thf('36', plain,
% 1.38/1.62      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         (~ (r2_hidden @ X19 @ X17)
% 1.38/1.62          | ~ (r2_hidden @ X19 @ X20)
% 1.38/1.62          | ~ (r1_xboole_0 @ X17 @ X20))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.62  thf('37', plain,
% 1.38/1.62      (![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['35', '36'])).
% 1.38/1.62  thf('38', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ~ (r2_hidden @ sk_A @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['32', '37'])).
% 1.38/1.62  thf('39', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))
% 1.38/1.62           = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['8', '38'])).
% 1.38/1.62  thf('40', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.38/1.62           = (k3_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('41', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.38/1.62           = (k3_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('42', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.62           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['40', '41'])).
% 1.38/1.62  thf('43', plain,
% 1.38/1.62      (![X22 : $i, X23 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 1.38/1.62           = (k4_xboole_0 @ X22 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.38/1.62  thf('44', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.38/1.62           = (k4_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['42', '43'])).
% 1.38/1.62  thf('45', plain,
% 1.38/1.62      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.38/1.62      inference('sup+', [status(thm)], ['39', '44'])).
% 1.38/1.62  thf('46', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.38/1.62           = (k3_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('47', plain,
% 1.38/1.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 1.38/1.62         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.38/1.62      inference('sup+', [status(thm)], ['45', '46'])).
% 1.38/1.62  thf(t3_boole, axiom,
% 1.38/1.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.38/1.62  thf('48', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_boole])).
% 1.38/1.62  thf(commutativity_k3_xboole_0, axiom,
% 1.38/1.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.38/1.62  thf('49', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.62  thf('50', plain,
% 1.38/1.62      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.38/1.62  thf('51', plain,
% 1.38/1.62      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('52', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.62  thf('53', plain,
% 1.38/1.62      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 1.38/1.62      inference('demod', [status(thm)], ['51', '52'])).
% 1.38/1.62  thf('54', plain, ($false),
% 1.38/1.62      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 1.38/1.62  
% 1.38/1.62  % SZS output end Refutation
% 1.38/1.62  
% 1.38/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
