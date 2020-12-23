%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9tHfdO1vjs

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:43 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 194 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  533 (1579 expanded)
%              Number of equality atoms :   46 ( 123 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ ( sk_D @ X14 @ X13 @ X12 ) @ X14 )
      | ( X12
        = ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ ( sk_D @ X14 @ X13 @ X12 ) @ X14 )
      | ( X12
        = ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_B_1 @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_tarski @ ( sk_D @ X14 @ X13 @ X12 ) @ X12 )
      | ( X12
        = ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('13',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
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

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('27',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( sk_D @ sk_A @ sk_C_1 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_tarski @ ( sk_D @ X14 @ X13 @ X12 ) @ X12 )
      | ( X12
        = ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('51',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','45'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9tHfdO1vjs
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.27  % Solved by: fo/fo7.sh
% 1.05/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.27  % done 2196 iterations in 0.821s
% 1.05/1.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.27  % SZS output start Refutation
% 1.05/1.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.27  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.27  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.05/1.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.27  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.27  thf(t3_boole, axiom,
% 1.05/1.27    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.05/1.27  thf('0', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.05/1.27      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.27  thf(t36_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.05/1.27  thf('1', plain,
% 1.05/1.27      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.05/1.27      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.27  thf('2', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.27      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.27  thf(t67_xboole_1, conjecture,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.05/1.27         ( r1_xboole_0 @ B @ C ) ) =>
% 1.05/1.27       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.27    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.27        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.05/1.27            ( r1_xboole_0 @ B @ C ) ) =>
% 1.05/1.27          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 1.05/1.27    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 1.05/1.27  thf('3', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(t20_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.05/1.27         ( ![D:$i]:
% 1.05/1.27           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 1.05/1.27             ( r1_tarski @ D @ A ) ) ) ) =>
% 1.05/1.27       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.05/1.27  thf('4', plain,
% 1.05/1.27      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.27         (~ (r1_tarski @ X12 @ X13)
% 1.05/1.27          | ~ (r1_tarski @ X12 @ X14)
% 1.05/1.27          | (r1_tarski @ (sk_D @ X14 @ X13 @ X12) @ X14)
% 1.05/1.27          | ((X12) = (k3_xboole_0 @ X13 @ X14)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t20_xboole_1])).
% 1.05/1.27  thf('5', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (((sk_A) = (k3_xboole_0 @ sk_C_1 @ X0))
% 1.05/1.27          | (r1_tarski @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ X0)
% 1.05/1.27          | ~ (r1_tarski @ sk_A @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.27  thf('6', plain,
% 1.05/1.27      (((r1_tarski @ (sk_D @ sk_A @ sk_C_1 @ sk_A) @ sk_A)
% 1.05/1.27        | ((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['2', '5'])).
% 1.05/1.27  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.27      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.27  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('9', plain,
% 1.05/1.27      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.27         (~ (r1_tarski @ X12 @ X13)
% 1.05/1.27          | ~ (r1_tarski @ X12 @ X14)
% 1.05/1.27          | (r1_tarski @ (sk_D @ X14 @ X13 @ X12) @ X14)
% 1.05/1.27          | ((X12) = (k3_xboole_0 @ X13 @ X14)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t20_xboole_1])).
% 1.05/1.27  thf('10', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (((sk_A) = (k3_xboole_0 @ sk_B_1 @ X0))
% 1.05/1.27          | (r1_tarski @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)
% 1.05/1.27          | ~ (r1_tarski @ sk_A @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.27  thf('11', plain,
% 1.05/1.27      (((r1_tarski @ (sk_D @ sk_A @ sk_B_1 @ sk_A) @ sk_A)
% 1.05/1.27        | ((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['7', '10'])).
% 1.05/1.27  thf('12', plain,
% 1.05/1.27      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.27         (~ (r1_tarski @ X12 @ X13)
% 1.05/1.27          | ~ (r1_tarski @ X12 @ X14)
% 1.05/1.27          | ~ (r1_tarski @ (sk_D @ X14 @ X13 @ X12) @ X12)
% 1.05/1.27          | ((X12) = (k3_xboole_0 @ X13 @ X14)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t20_xboole_1])).
% 1.05/1.27  thf('13', plain,
% 1.05/1.27      ((((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.27        | ((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.27        | ~ (r1_tarski @ sk_A @ sk_A)
% 1.05/1.27        | ~ (r1_tarski @ sk_A @ sk_B_1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['11', '12'])).
% 1.05/1.27  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.27      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.27  thf('15', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('16', plain,
% 1.05/1.27      ((((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.27        | ((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.05/1.27  thf('17', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 1.05/1.27      inference('simplify', [status(thm)], ['16'])).
% 1.05/1.27  thf('18', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(symmetry_r1_xboole_0, axiom,
% 1.05/1.27    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.05/1.27  thf('19', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.27      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.05/1.27  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 1.05/1.27      inference('sup-', [status(thm)], ['18', '19'])).
% 1.05/1.27  thf(t7_xboole_0, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.05/1.27          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.05/1.27  thf('21', plain,
% 1.05/1.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.05/1.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.05/1.27  thf(t4_xboole_0, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.27            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.27       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.27            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.27  thf('22', plain,
% 1.05/1.27      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.05/1.27         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.05/1.27          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.05/1.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.27  thf('23', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.27  thf('24', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.27  thf('25', plain,
% 1.05/1.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.05/1.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.05/1.27  thf(t16_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.05/1.27       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.05/1.27  thf('26', plain,
% 1.05/1.27      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.05/1.27           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.05/1.27  thf('27', plain,
% 1.05/1.27      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.05/1.27         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.05/1.27          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.05/1.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.27  thf('28', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.27         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.05/1.27          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.27  thf('29', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.27         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 1.05/1.27          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['25', '28'])).
% 1.05/1.27  thf('30', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 1.05/1.27          | ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B_1 @ X0))
% 1.05/1.27              = (k1_xboole_0)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['24', '29'])).
% 1.05/1.27  thf(t51_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.05/1.27       ( A ) ))).
% 1.05/1.27  thf('31', plain,
% 1.05/1.27      (![X18 : $i, X19 : $i]:
% 1.05/1.27         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.05/1.27           = (X18))),
% 1.05/1.27      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.05/1.27  thf(t15_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.27       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.27  thf('32', plain,
% 1.05/1.27      (![X7 : $i, X8 : $i]:
% 1.05/1.27         (((X7) = (k1_xboole_0)) | ((k2_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t15_xboole_1])).
% 1.05/1.27  thf('33', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         (((X0) != (k1_xboole_0)) | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['31', '32'])).
% 1.05/1.27  thf('34', plain,
% 1.05/1.27      (![X1 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 1.05/1.27      inference('simplify', [status(thm)], ['33'])).
% 1.05/1.27  thf('35', plain,
% 1.05/1.27      (![X2 : $i, X3 : $i]:
% 1.05/1.27         ((r1_xboole_0 @ X2 @ X3)
% 1.05/1.27          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.27  thf('36', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.05/1.27          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup+', [status(thm)], ['34', '35'])).
% 1.05/1.27  thf('37', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('38', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.27  thf('39', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.27  thf('40', plain,
% 1.05/1.27      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.05/1.27         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.05/1.27          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.05/1.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.27  thf('41', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.27  thf('42', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.05/1.27      inference('demod', [status(thm)], ['41', '42'])).
% 1.05/1.27  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.05/1.27      inference('clc', [status(thm)], ['36', '43'])).
% 1.05/1.27  thf('45', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B_1 @ X0)) = (k1_xboole_0))),
% 1.05/1.27      inference('demod', [status(thm)], ['30', '44'])).
% 1.05/1.27  thf('46', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.05/1.27      inference('sup+', [status(thm)], ['17', '45'])).
% 1.05/1.27  thf('47', plain,
% 1.05/1.27      (((r1_tarski @ (sk_D @ sk_A @ sk_C_1 @ sk_A) @ sk_A)
% 1.05/1.27        | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.27      inference('demod', [status(thm)], ['6', '46'])).
% 1.05/1.27  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('49', plain, ((r1_tarski @ (sk_D @ sk_A @ sk_C_1 @ sk_A) @ sk_A)),
% 1.05/1.27      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 1.05/1.27  thf('50', plain,
% 1.05/1.27      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.27         (~ (r1_tarski @ X12 @ X13)
% 1.05/1.27          | ~ (r1_tarski @ X12 @ X14)
% 1.05/1.27          | ~ (r1_tarski @ (sk_D @ X14 @ X13 @ X12) @ X12)
% 1.05/1.27          | ((X12) = (k3_xboole_0 @ X13 @ X14)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t20_xboole_1])).
% 1.05/1.27  thf('51', plain,
% 1.05/1.27      ((((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))
% 1.05/1.27        | ~ (r1_tarski @ sk_A @ sk_A)
% 1.05/1.27        | ~ (r1_tarski @ sk_A @ sk_C_1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.27  thf('52', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.05/1.27      inference('sup+', [status(thm)], ['17', '45'])).
% 1.05/1.27  thf('53', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.27      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.27  thf('54', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.27      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.05/1.27  thf('56', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('57', plain, ($false),
% 1.05/1.27      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 1.05/1.27  
% 1.05/1.27  % SZS output end Refutation
% 1.05/1.27  
% 1.05/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
