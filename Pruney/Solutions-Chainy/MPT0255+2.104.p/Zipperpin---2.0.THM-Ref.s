%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NyLm6n8ERP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  469 ( 870 expanded)
%              Number of equality atoms :   56 ( 112 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ( r2_hidden @ X28 @ X29 )
      | ( X29
       != ( k2_tarski @ X30 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('40',plain,(
    ! [X27: $i,X30: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X30 @ X27 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('48',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['43','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NyLm6n8ERP
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:48:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 210 iterations in 0.111s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(t50_zfmisc_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t98_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X25 @ X26)
% 0.20/0.56           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('3', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.20/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf(t3_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('8', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf(t48_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.20/0.56           = (k3_xboole_0 @ X19 @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf(t2_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.56  thf(t91_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.20/0.56           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X25 @ X26)
% 0.20/0.56           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.56  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('26', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf('27', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['22', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['19', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['1', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.20/0.56         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['0', '30'])).
% 0.20/0.56  thf('32', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.20/0.56         = (k2_tarski @ sk_A @ sk_B_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.56  thf(t39_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.20/0.56           = (k2_xboole_0 @ X16 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.20/0.56         (k2_tarski @ sk_A @ sk_B_1))
% 0.20/0.56         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.56  thf('36', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.56  thf(d2_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.56         (((X28) != (X27))
% 0.20/0.56          | (r2_hidden @ X28 @ X29)
% 0.20/0.56          | ((X29) != (k2_tarski @ X30 @ X27)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X27 : $i, X30 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X30 @ X27))),
% 0.20/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.56  thf(d1_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.56  thf('43', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf(t4_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.20/0.56          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.56  thf('48', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.56  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.20/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['43', '50'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
