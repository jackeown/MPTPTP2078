%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5svHkiYyQ8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:24 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 219 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  515 (1589 expanded)
%              Number of equality atoms :   51 ( 129 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 )
        = sk_A )
      | ~ ( v1_zfmisc_1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 )
        = sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 )
        = sk_A )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['8','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ sk_A @ sk_A ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('50',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('52',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5svHkiYyQ8
% 0.14/0.38  % Computer   : n003.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 18:31:42 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 456 iterations in 0.187s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t2_tex_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.46/0.64           ( r1_tarski @ A @ B ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.46/0.64              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.46/0.64  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.46/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.64  thf(l32_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X10 : $i, X12 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf(t3_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('7', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('8', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf(t17_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.64  thf(t1_tex_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.46/0.64           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X33)
% 0.46/0.64          | ~ (v1_zfmisc_1 @ X33)
% 0.46/0.64          | ((X34) = (X33))
% 0.46/0.64          | ~ (r1_tarski @ X34 @ X33)
% 0.46/0.64          | (v1_xboole_0 @ X34))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.46/0.64          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.46/0.64          | ~ (v1_zfmisc_1 @ X0)
% 0.46/0.64          | (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_A)
% 0.46/0.64        | ~ (v1_zfmisc_1 @ sk_A)
% 0.46/0.64        | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf('14', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('16', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf(t51_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.46/0.64       ( A ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.64  thf(t10_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X13 @ X14)
% 0.46/0.64          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0) @ sk_A)),
% 0.46/0.64      inference('sup+', [status(thm)], ['19', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X33)
% 0.46/0.64          | ~ (v1_zfmisc_1 @ X33)
% 0.46/0.64          | ((X34) = (X33))
% 0.46/0.64          | ~ (r1_tarski @ X34 @ X33)
% 0.46/0.64          | (v1_xboole_0 @ X34))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0))
% 0.46/0.64          | ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0) = (sk_A))
% 0.46/0.64          | ~ (v1_zfmisc_1 @ sk_A)
% 0.46/0.64          | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0))
% 0.46/0.64          | ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0) = (sk_A))
% 0.46/0.64          | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0) = (sk_A))
% 0.46/0.64          | (v1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.46/0.64        | ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 0.46/0.64            (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['8', '29'])).
% 0.46/0.64  thf('31', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X4 : $i, X6 : $i]:
% 0.46/0.64         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf(d1_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf(t2_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.64  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X7 : $i, X9 : $i]:
% 0.46/0.64         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      ((((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.46/0.64          = (k3_xboole_0 @ sk_A @ sk_A))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.64  thf('47', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('49', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((((k1_xboole_0) = (sk_A))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '41'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((((sk_A) != (k1_xboole_0))
% 0.46/0.64        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('eq_fact', [status(thm)], ['51'])).
% 0.46/0.64  thf('53', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.64      inference('clc', [status(thm)], ['50', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         ((r1_tarski @ X10 @ X11)
% 0.46/0.64          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.64  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
