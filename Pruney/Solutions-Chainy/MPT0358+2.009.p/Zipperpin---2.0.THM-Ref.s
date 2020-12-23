%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CRriGeujcR

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  508 ( 971 expanded)
%              Number of equality atoms :   51 (  92 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('22',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('28',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('50',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B
       != ( k1_subset_1 @ sk_A ) )
      & ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CRriGeujcR
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 152 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(t38_subset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.51         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.51            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.20/0.51        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.51       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf(d1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X12 @ X13)
% 0.20/0.51          | (r2_hidden @ X12 @ X14)
% 0.20/0.51          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.51  thf(d2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X17 @ X18)
% 0.20/0.51          | (m1_subset_1 @ X17 @ X18)
% 0.20/0.51          | (v1_xboole_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(fc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('9', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(d5_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf(l32_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X5 : $i, X7 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.51  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.51  thf('20', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '19'])).
% 0.20/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('21', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.20/0.51        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.51         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.51             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '23'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.51         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.51             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.51         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.51             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '23'])).
% 0.20/0.51  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ X18)
% 0.20/0.51          | (r2_hidden @ X17 @ X18)
% 0.20/0.51          | (v1_xboole_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('35', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.51         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X15 @ X14)
% 0.20/0.51          | (r1_tarski @ X15 @ X13)
% 0.20/0.51          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X13 : $i, X15 : $i]:
% 0.20/0.51         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.51         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.51       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.51       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf(t38_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (((X10) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.20/0.51         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.51         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))) & 
% 0.20/0.51             ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.51       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
