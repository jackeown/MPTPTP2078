%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hmd40da69C

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 199 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  543 (1708 expanded)
%              Number of equality atoms :   56 ( 178 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('13',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ X0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['9','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','45'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = ( k3_subset_1 @ X22 @ ( k1_subset_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('48',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X16: $i] :
      ( ( k1_subset_1 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('50',plain,(
    ! [X22: $i] :
      ( X22
      = ( k3_subset_1 @ X22 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','46','50'])).

thf('52',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('53',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','32'])).

thf('56',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hmd40da69C
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 163 iterations in 0.076s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(t39_subset_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.53         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.53            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.21/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.21/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.21/0.53        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((r2_hidden @ X0 @ sk_B)
% 0.21/0.53           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.21/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.21/0.53        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.21/0.53       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.53      inference('split', [status(esa)], ['8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('11', plain, (![X17 : $i]: ((k2_subset_1 @ X17) = (X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf(d5_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf(d5_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.53          | (r2_hidden @ X8 @ X5)
% 0.21/0.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.53         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.21/0.53           | (r2_hidden @ X0 @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.21/0.53           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A)))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['20', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ X0))
% 0.21/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['8'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.21/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.21/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.21/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.21/0.53       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.21/0.53       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('34', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['9', '32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ sk_B)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['7', '34'])).
% 0.21/0.53  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['35', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '41'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('43', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i]:
% 0.21/0.53         (((X10) = (X12))
% 0.21/0.53          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.53          | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '45'])).
% 0.21/0.53  thf(t22_subset_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X22 : $i]:
% 0.21/0.53         ((k2_subset_1 @ X22) = (k3_subset_1 @ X22 @ (k1_subset_1 @ X22)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.53  thf('48', plain, (![X17 : $i]: ((k2_subset_1 @ X17) = (X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('49', plain, (![X16 : $i]: ((k1_subset_1 @ X16) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.53  thf('50', plain, (![X22 : $i]: ((X22) = (k3_subset_1 @ X22 @ k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.53  thf('51', plain, (((sk_A) = (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '46', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.21/0.53         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['8'])).
% 0.21/0.53  thf('53', plain, (![X17 : $i]: ((k2_subset_1 @ X17) = (X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['9', '32'])).
% 0.21/0.53  thf('56', plain, (((sk_B) != (sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.21/0.53  thf('57', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['51', '56'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
