%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r4Jx0Jc1J8

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 158 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  461 (1214 expanded)
%              Number of equality atoms :   42 ( 111 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('10',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k1_subset_1 @ sk_A ) ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('47',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['17','34','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','48'])).

thf('50',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['36','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r4Jx0Jc1J8
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 191 iterations in 0.080s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('1', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf(d5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X13 @ X12)
% 0.20/0.53          | ~ (r2_hidden @ X13 @ X11)
% 0.20/0.53          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X13 @ X11)
% 0.20/0.53          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.53  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.53      inference('condensation', [status(thm)], ['4'])).
% 0.20/0.53  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf(l13_xboole_0, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf(t38_subset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.53         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.53            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((sk_B_1) != (X0))
% 0.20/0.53           | ~ (v1_xboole_0 @ X0)
% 0.20/0.53           | ~ (v1_xboole_0 @ (k1_subset_1 @ sk_A))))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('13', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((sk_B_1) != (X0))
% 0.20/0.53           | ~ (v1_xboole_0 @ X0)
% 0.20/0.53           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['10'])).
% 0.20/0.53  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X6 : $i, X8 : $i]:
% 0.20/0.53         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.53  thf('23', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.20/0.53        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.20/0.53         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['10'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.20/0.53           | ~ (v1_xboole_0 @ X0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '33'])).
% 0.20/0.53  thf('35', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['17', '34'])).
% 0.20/0.53  thf('36', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['16', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X13 @ X11)
% 0.20/0.53          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.53          | (r2_hidden @ X5 @ X7)
% 0.20/0.53          | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['24'])).
% 0.20/0.53  thf('47', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['17', '34', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['45', '47'])).
% 0.20/0.53  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.20/0.53      inference('clc', [status(thm)], ['42', '48'])).
% 0.20/0.53  thf('50', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '49'])).
% 0.20/0.53  thf('51', plain, ($false), inference('demod', [status(thm)], ['36', '50'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
