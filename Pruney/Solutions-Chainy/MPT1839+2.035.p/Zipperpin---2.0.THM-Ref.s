%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MkcoozOAGf

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:27 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 ( 747 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i] :
      ( ( v1_xboole_0 @ X51 )
      | ~ ( v1_zfmisc_1 @ X51 )
      | ( X52 = X51 )
      | ~ ( r1_tarski @ X52 @ X51 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r1_tarski @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MkcoozOAGf
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 211 iterations in 0.077s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.36/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.53  thf(t2_tex_2, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.36/0.53           ( r1_tarski @ A @ B ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.36/0.53              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.36/0.53  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t17_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.36/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.53  thf(t1_tex_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.36/0.53           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (![X51 : $i, X52 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ X51)
% 0.36/0.53          | ~ (v1_zfmisc_1 @ X51)
% 0.36/0.53          | ((X52) = (X51))
% 0.36/0.53          | ~ (r1_tarski @ X52 @ X51)
% 0.36/0.53          | (v1_xboole_0 @ X52))),
% 0.36/0.53      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.36/0.53          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.36/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.36/0.53          | (v1_xboole_0 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.53  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (((v1_xboole_0 @ sk_A)
% 0.36/0.53        | ~ (v1_zfmisc_1 @ sk_A)
% 0.36/0.53        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.53  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.53  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['7', '8'])).
% 0.36/0.53  thf(t100_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i]:
% 0.36/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.36/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.36/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.53  thf(t2_tarski, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.36/0.53       ( ( A ) = ( B ) ) ))).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         (((X12) = (X11))
% 0.36/0.53          | (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 0.36/0.53          | (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.53  thf('13', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.36/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.53  thf(d5_xboole_0, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.53       ( ![D:$i]:
% 0.36/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.36/0.53         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.36/0.53          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.36/0.53          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.36/0.53          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.53      inference('eq_fact', [status(thm)], ['14'])).
% 0.36/0.53  thf(t7_ordinal1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X49 : $i, X50 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X49 @ X50) | ~ (r1_tarski @ X50 @ X49))),
% 0.36/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.36/0.53          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['13', '17'])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.36/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.36/0.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.36/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['18', '20'])).
% 0.36/0.53  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.53      inference('condensation', [status(thm)], ['21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.36/0.54          | ((X0) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '22'])).
% 0.36/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.54  thf('24', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ X13 @ X14)
% 0.36/0.54           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf(t36_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.36/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.54  thf(d3_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.54          | (r2_hidden @ X0 @ X2)
% 0.36/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.36/0.54          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.36/0.54          | ~ (r2_hidden @ X1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['30', '33'])).
% 0.36/0.54  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '34'])).
% 0.36/0.54  thf('36', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.36/0.54          | (r2_hidden @ X4 @ X6)
% 0.36/0.54          | (r2_hidden @ X4 @ X7)
% 0.36/0.54          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.36/0.54          | (r2_hidden @ X4 @ X6)
% 0.36/0.54          | ~ (r2_hidden @ X4 @ X5))),
% 0.36/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((r1_tarski @ X0 @ X1)
% 0.36/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.36/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '39'])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.36/0.54          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.36/0.54          | (r1_tarski @ sk_A @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['36', '40'])).
% 0.36/0.54  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('condensation', [status(thm)], ['21'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.36/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.54  thf('45', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.54  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.54  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
