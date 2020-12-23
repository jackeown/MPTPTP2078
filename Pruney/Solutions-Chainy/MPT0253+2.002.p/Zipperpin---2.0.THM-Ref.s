%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D93QQBjBhb

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:30 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 103 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 ( 718 expanded)
%              Number of equality atoms :   44 (  67 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X29: $i] :
      ( r1_tarski @ k1_xboole_0 @ X29 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ X15 @ X12 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','36'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X26: $i] :
      ( ( k2_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D93QQBjBhb
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.63/0.82  % Solved by: fo/fo7.sh
% 0.63/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.82  % done 790 iterations in 0.366s
% 0.63/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.63/0.82  % SZS output start Refutation
% 0.63/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.63/0.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.63/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.63/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.63/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.63/0.82  thf(t48_zfmisc_1, conjecture,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.63/0.82       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.63/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.63/0.82        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.63/0.82          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.63/0.82    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.63/0.82  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t38_zfmisc_1, axiom,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.63/0.82       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.63/0.82  thf('2', plain,
% 0.63/0.82      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.63/0.82         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 0.63/0.82          | ~ (r2_hidden @ X47 @ X48)
% 0.63/0.82          | ~ (r2_hidden @ X45 @ X48))),
% 0.63/0.82      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.63/0.82  thf('3', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.63/0.82          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.63/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.63/0.82  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_A) @ sk_B_1)),
% 0.63/0.82      inference('sup-', [status(thm)], ['0', '3'])).
% 0.63/0.82  thf(commutativity_k2_tarski, axiom,
% 0.63/0.82    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.63/0.82  thf('5', plain,
% 0.63/0.82      (![X32 : $i, X33 : $i]:
% 0.63/0.82         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.63/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.63/0.82  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)),
% 0.63/0.82      inference('demod', [status(thm)], ['4', '5'])).
% 0.63/0.82  thf(t28_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.63/0.82  thf('7', plain,
% 0.63/0.82      (![X27 : $i, X28 : $i]:
% 0.63/0.82         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.63/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.63/0.82  thf('8', plain,
% 0.63/0.82      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 0.63/0.82         = (k2_tarski @ sk_A @ sk_C_2))),
% 0.63/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.82  thf(t100_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.63/0.82  thf('9', plain,
% 0.63/0.82      (![X24 : $i, X25 : $i]:
% 0.63/0.82         ((k4_xboole_0 @ X24 @ X25)
% 0.63/0.82           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.63/0.82  thf('10', plain,
% 0.63/0.82      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 0.63/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ 
% 0.63/0.82            (k2_tarski @ sk_A @ sk_C_2)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['8', '9'])).
% 0.63/0.82  thf(t2_tarski, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.63/0.82       ( ( A ) = ( B ) ) ))).
% 0.63/0.82  thf('11', plain,
% 0.63/0.82      (![X18 : $i, X19 : $i]:
% 0.63/0.82         (((X19) = (X18))
% 0.63/0.82          | (r2_hidden @ (sk_C @ X18 @ X19) @ X18)
% 0.63/0.82          | (r2_hidden @ (sk_C @ X18 @ X19) @ X19))),
% 0.63/0.82      inference('cnf', [status(esa)], [t2_tarski])).
% 0.63/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.63/0.82  thf('12', plain, (![X29 : $i]: (r1_tarski @ k1_xboole_0 @ X29)),
% 0.63/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.63/0.82  thf('13', plain,
% 0.63/0.82      (![X27 : $i, X28 : $i]:
% 0.63/0.82         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.63/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.63/0.82  thf('14', plain,
% 0.63/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.63/0.82  thf('15', plain,
% 0.63/0.82      (![X24 : $i, X25 : $i]:
% 0.63/0.82         ((k4_xboole_0 @ X24 @ X25)
% 0.63/0.82           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.63/0.82  thf('16', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.63/0.82           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['14', '15'])).
% 0.63/0.82  thf(idempotence_k3_xboole_0, axiom,
% 0.63/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.63/0.82  thf('17', plain, (![X17 : $i]: ((k3_xboole_0 @ X17 @ X17) = (X17))),
% 0.63/0.82      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.63/0.82  thf('18', plain,
% 0.63/0.82      (![X24 : $i, X25 : $i]:
% 0.63/0.82         ((k4_xboole_0 @ X24 @ X25)
% 0.63/0.82           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.63/0.82  thf('19', plain,
% 0.63/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.63/0.82  thf(d5_xboole_0, axiom,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.63/0.82       ( ![D:$i]:
% 0.63/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.63/0.82           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.63/0.82  thf('20', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X15 @ X14)
% 0.63/0.82          | ~ (r2_hidden @ X15 @ X13)
% 0.63/0.82          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.82  thf('21', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X15 @ X13)
% 0.63/0.82          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['20'])).
% 0.63/0.82  thf('22', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.63/0.82          | ~ (r2_hidden @ X1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['19', '21'])).
% 0.63/0.82  thf('23', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.63/0.82          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['16', '22'])).
% 0.63/0.82  thf('24', plain,
% 0.63/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.63/0.82  thf(d4_xboole_0, axiom,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.63/0.82       ( ![D:$i]:
% 0.63/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.63/0.82           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.63/0.82  thf('25', plain,
% 0.63/0.82      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X9 @ X8)
% 0.63/0.82          | (r2_hidden @ X9 @ X7)
% 0.63/0.82          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.63/0.82  thf('26', plain,
% 0.63/0.82      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.63/0.82         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['25'])).
% 0.63/0.82  thf('27', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['24', '26'])).
% 0.63/0.82  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.63/0.82      inference('clc', [status(thm)], ['23', '27'])).
% 0.63/0.82  thf('29', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['11', '28'])).
% 0.63/0.82  thf('30', plain,
% 0.63/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.63/0.82  thf('31', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X15 @ X14)
% 0.63/0.82          | (r2_hidden @ X15 @ X12)
% 0.63/0.82          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.82  thf('32', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.63/0.82         ((r2_hidden @ X15 @ X12)
% 0.63/0.82          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.63/0.82  thf('33', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['30', '32'])).
% 0.63/0.82  thf('34', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.63/0.82          | ~ (r2_hidden @ X1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['19', '21'])).
% 0.63/0.82  thf('35', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.63/0.82      inference('clc', [status(thm)], ['33', '34'])).
% 0.63/0.82  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['29', '35'])).
% 0.63/0.82  thf('37', plain,
% 0.63/0.82      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) = (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['10', '36'])).
% 0.63/0.82  thf(t39_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('38', plain,
% 0.63/0.82      (![X30 : $i, X31 : $i]:
% 0.63/0.82         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 0.63/0.82           = (k2_xboole_0 @ X30 @ X31))),
% 0.63/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.63/0.82  thf('39', plain,
% 0.63/0.82      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.63/0.82         = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['37', '38'])).
% 0.63/0.82  thf(t1_boole, axiom,
% 0.63/0.82    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.63/0.82  thf('40', plain, (![X26 : $i]: ((k2_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.63/0.82      inference('cnf', [status(esa)], [t1_boole])).
% 0.63/0.82  thf('41', plain,
% 0.63/0.82      (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 0.63/0.82      inference('demod', [status(thm)], ['39', '40'])).
% 0.63/0.82  thf('42', plain,
% 0.63/0.82      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) != (sk_B_1))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('43', plain,
% 0.63/0.82      (![X32 : $i, X33 : $i]:
% 0.63/0.82         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.63/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.63/0.82  thf(l51_zfmisc_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('44', plain,
% 0.63/0.82      (![X43 : $i, X44 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.63/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.63/0.82  thf('45', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['43', '44'])).
% 0.63/0.82  thf('46', plain,
% 0.63/0.82      (![X43 : $i, X44 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.63/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.63/0.82  thf('47', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['45', '46'])).
% 0.63/0.82  thf('48', plain,
% 0.63/0.82      (((k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)) != (sk_B_1))),
% 0.63/0.82      inference('demod', [status(thm)], ['42', '47'])).
% 0.63/0.82  thf('49', plain, ($false),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['41', '48'])).
% 0.63/0.82  
% 0.63/0.82  % SZS output end Refutation
% 0.63/0.82  
% 0.63/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
