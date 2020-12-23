%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYyXSm57Yt

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 140 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  503 (1153 expanded)
%              Number of equality atoms :   29 ( 101 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X21 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('21',plain,
    ( ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_3 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('25',plain,(
    r2_hidden @ ( sk_C_3 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_3 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X21 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_3 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_3 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_C_3 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['25','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( sk_C_3 @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('50',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYyXSm57Yt
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 162 iterations in 0.125s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.58  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.58  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(t2_tarski, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.58       ( ( A ) = ( B ) ) ))).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (![X7 : $i, X8 : $i]:
% 0.22/0.58         (((X8) = (X7))
% 0.22/0.58          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.22/0.58          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.58  thf(t2_boole, axiom,
% 0.22/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.58  thf(t4_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.22/0.58          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.22/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.58  thf('4', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.22/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.58  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.58  thf('6', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.58          | ((k1_xboole_0) = (X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.58  thf(d3_tarski, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (![X1 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf(l54_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.22/0.58         ((r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X21))
% 0.22/0.58          | ~ (r2_hidden @ X19 @ X21)
% 0.22/0.58          | ~ (r2_hidden @ X17 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X0 @ X1)
% 0.22/0.58          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.58          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.22/0.58             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (X0))
% 0.22/0.58          | (r2_hidden @ 
% 0.22/0.58             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.22/0.58             (k2_zfmisc_1 @ X0 @ X1))
% 0.22/0.58          | (r1_tarski @ X1 @ X2))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.58  thf(t114_zfmisc_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.22/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58         ( ( A ) = ( B ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i]:
% 0.22/0.58        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.22/0.58          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58            ( ( A ) = ( B ) ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.58         ((r2_hidden @ X19 @ X20)
% 0.22/0.58          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X20)))),
% 0.22/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.58  thf('13', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.58          | (r2_hidden @ X0 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r1_tarski @ sk_B @ X0)
% 0.22/0.58          | ((k1_xboole_0) = (sk_A))
% 0.22/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.58  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X1 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf('18', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.58  thf('19', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.58  thf(d8_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.58       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i]:
% 0.22/0.58         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.58  thf('21', plain, ((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.58  thf('22', plain, (((sk_A) != (sk_B))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('23', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf(t6_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.22/0.58          ( ![C:$i]:
% 0.22/0.58            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (~ (r2_xboole_0 @ X13 @ X14)
% 0.22/0.58          | (r2_hidden @ (sk_C_3 @ X14 @ X13) @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.58  thf('25', plain, ((r2_hidden @ (sk_C_3 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      (![X1 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      (![X1 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.58  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i]:
% 0.22/0.58         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (~ (r2_xboole_0 @ X13 @ X14)
% 0.22/0.58          | (r2_hidden @ (sk_C_3 @ X14 @ X13) @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.58  thf('33', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (X0))
% 0.22/0.58          | (r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.22/0.58         ((r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X21))
% 0.22/0.58          | ~ (r2_hidden @ X19 @ X21)
% 0.22/0.58          | ~ (r2_hidden @ X17 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (X0))
% 0.22/0.58          | ~ (r2_hidden @ X2 @ X1)
% 0.22/0.58          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_3 @ X0 @ k1_xboole_0)) @ 
% 0.22/0.58             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         ((r1_tarski @ X0 @ X1)
% 0.22/0.58          | (r2_hidden @ 
% 0.22/0.58             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_3 @ X2 @ k1_xboole_0)) @ 
% 0.22/0.58             (k2_zfmisc_1 @ X0 @ X2))
% 0.22/0.58          | ((k1_xboole_0) = (X2)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['26', '35'])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.58         ((r2_hidden @ X17 @ X18)
% 0.22/0.58          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X20)))),
% 0.22/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.58          | (r2_hidden @ X1 @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (sk_B))
% 0.22/0.58          | (r1_tarski @ sk_A @ X0)
% 0.22/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['36', '39'])).
% 0.22/0.58  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('42', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (![X1 : $i, X3 : $i]:
% 0.22/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf('44', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.58  thf('45', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.58          | (r2_hidden @ X0 @ X2)
% 0.22/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.58  thf('48', plain, ((r2_hidden @ (sk_C_3 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.58      inference('sup-', [status(thm)], ['25', '47'])).
% 0.22/0.58  thf('49', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i]:
% 0.22/0.58         (~ (r2_xboole_0 @ X13 @ X14)
% 0.22/0.58          | ~ (r2_hidden @ (sk_C_3 @ X14 @ X13) @ X13))),
% 0.22/0.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.58  thf('50', plain, (~ (r2_xboole_0 @ sk_B @ sk_A)),
% 0.22/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.58  thf('51', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('52', plain, ($false), inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
