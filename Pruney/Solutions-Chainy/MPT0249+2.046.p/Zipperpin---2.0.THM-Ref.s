%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3Y1nFpvAC

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 219 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  583 (1924 expanded)
%              Number of equality atoms :   77 ( 358 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ sk_B_1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('41',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['27','41'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ sk_C_2 )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['27','41'])).

thf('59',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['8','61'])).

thf('63',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3Y1nFpvAC
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 440 iterations in 0.227s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.68  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(t7_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.68  thf(t44_zfmisc_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.68          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.68        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.68             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.46/0.68  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(l3_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X33 : $i, X34 : $i]:
% 0.46/0.68         (((X34) = (k1_tarski @ X33))
% 0.46/0.68          | ((X34) = (k1_xboole_0))
% 0.46/0.68          | ~ (r1_tarski @ X34 @ (k1_tarski @ X33)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.46/0.68          | ((X0) = (k1_xboole_0))
% 0.46/0.68          | ((X0) = (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.46/0.68          | ((X0) = (k1_xboole_0))
% 0.46/0.68          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.46/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.46/0.68        | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.68  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf(t7_xboole_0, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X10 : $i]:
% 0.46/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X10 : $i]:
% 0.46/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.68  thf(d5_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X4 @ X5)
% 0.46/0.68          | (r2_hidden @ X4 @ X6)
% 0.46/0.68          | (r2_hidden @ X4 @ X7)
% 0.46/0.68          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.68         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.46/0.68          | (r2_hidden @ X4 @ X6)
% 0.46/0.68          | ~ (r2_hidden @ X4 @ X5))),
% 0.46/0.68      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((X0) = (k1_xboole_0))
% 0.46/0.68          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.46/0.68          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.68  thf('14', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf(t41_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.68       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.68           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X8 @ X7)
% 0.46/0.68          | ~ (r2_hidden @ X8 @ X6)
% 0.46/0.68          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.68          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.46/0.68          | ~ (r2_hidden @ X3 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['15', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_B_1))
% 0.46/0.68          | ~ (r2_hidden @ X1 @ sk_C_2))),
% 0.46/0.68      inference('sup-', [status(thm)], ['14', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_B @ X0) @ sk_B_1)
% 0.46/0.68          | ((X0) = (k1_xboole_0))
% 0.46/0.68          | ~ (r2_hidden @ (sk_B @ X0) @ sk_C_2))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '19'])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      ((((sk_C_2) = (k1_xboole_0))
% 0.46/0.68        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.68        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.68  thf('23', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('24', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('25', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('26', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('27', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('28', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t69_enumset1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.68  thf(l51_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X36 : $i, X37 : $i]:
% 0.46/0.68         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 0.46/0.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf(d3_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X1 : $i, X3 : $i]:
% 0.46/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X1 : $i, X3 : $i]:
% 0.46/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.68  thf(t12_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i]:
% 0.46/0.68         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.68  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['31', '37'])).
% 0.46/0.68  thf('39', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)) = (sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['28', '38'])).
% 0.46/0.68  thf('40', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('41', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.68  thf('42', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['27', '41'])).
% 0.46/0.68  thf(d1_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X21 @ X20)
% 0.46/0.68          | ((X21) = (X18))
% 0.46/0.68          | ((X20) != (k1_tarski @ X18)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X18 : $i, X21 : $i]:
% 0.46/0.68         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['42', '44'])).
% 0.46/0.68  thf('46', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['24', '45'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (![X10 : $i]:
% 0.46/0.68         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (![X1 : $i, X3 : $i]:
% 0.46/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X18 : $i, X21 : $i]:
% 0.46/0.68         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.68          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X1 : $i, X3 : $i]:
% 0.46/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.68          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.68          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['47', '53'])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i]:
% 0.46/0.68         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((X0) = (k1_xboole_0))
% 0.46/0.68          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((((k2_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ sk_C_2) = (sk_C_2))
% 0.46/0.68        | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['46', '56'])).
% 0.46/0.68  thf('58', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['27', '41'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      ((((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 0.46/0.68        | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.68  thf('60', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('61', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('62', plain, (((sk_B_1) = (sk_C_2))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '61'])).
% 0.46/0.68  thf('63', plain, (((sk_B_1) != (sk_C_2))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('64', plain, ($false),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
