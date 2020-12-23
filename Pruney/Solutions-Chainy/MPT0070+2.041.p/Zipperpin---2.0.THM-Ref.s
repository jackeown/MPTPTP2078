%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b2cNKKYSMS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 170 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  470 (1155 expanded)
%              Number of equality atoms :   43 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['40','41','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('57',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b2cNKKYSMS
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 324 iterations in 0.099s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(t63_xboole_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.55          ( r1_xboole_0 @ A @ C ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.20/0.55  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(l32_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.55  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf(t39_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.20/0.55           = (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf(t1_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('6', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.55  thf('7', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.55  thf('10', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(t7_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.55  thf(t4_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.55  thf(t47_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.20/0.55           = (k4_xboole_0 @ X18 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf(t3_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('17', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('18', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf(t41_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.55       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.20/0.55           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.20/0.55           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['7', '20'])).
% 0.20/0.55  thf(t48_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.20/0.55           = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A))
% 0.20/0.55         = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.20/0.55           = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('25', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.55  thf('26', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X2 @ X3)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('28', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.20/0.55           = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf(t2_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.55  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.20/0.55           = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('36', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0)
% 0.20/0.55        | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '39'])).
% 0.20/0.55  thf('41', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X2 @ X3)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.55          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('47', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.55  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.55  thf('57', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.55  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
