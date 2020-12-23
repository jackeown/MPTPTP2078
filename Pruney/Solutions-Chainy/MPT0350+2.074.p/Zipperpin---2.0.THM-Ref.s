%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GsF4IoyqgA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 147 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  513 (1075 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( r1_tarski @ X26 @ X24 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ X26 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X25 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['32','38'])).

thf('40',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GsF4IoyqgA
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 202 iterations in 0.095s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(d3_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i]:
% 0.20/0.55         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf(t25_subset_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.55         ( k2_subset_1 @ A ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.55            ( k2_subset_1 @ A ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.20/0.55  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d2_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X30 @ X31)
% 0.20/0.55          | (r2_hidden @ X30 @ X31)
% 0.20/0.55          | (v1_xboole_0 @ X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf(fc1_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('4', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.55  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf(d1_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X26 @ X25)
% 0.20/0.55          | (r1_tarski @ X26 @ X24)
% 0.20/0.55          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X24 : $i, X26 : $i]:
% 0.20/0.55         ((r1_tarski @ X26 @ X24) | ~ (r2_hidden @ X26 @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.55  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.55  thf(t28_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X12 @ X13)
% 0.20/0.55           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.55  thf(d5_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.55          | (r2_hidden @ X10 @ X7)
% 0.20/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         ((r2_hidden @ X10 @ X7)
% 0.20/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.55          | (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i]:
% 0.20/0.55         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.55        | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X23 @ X24)
% 0.20/0.55          | (r2_hidden @ X23 @ X25)
% 0.20/0.55          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i]:
% 0.20/0.55         ((r2_hidden @ X23 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((r2_hidden @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X30 @ X31)
% 0.20/0.55          | (m1_subset_1 @ X30 @ X31)
% 0.20/0.55          | (v1_xboole_0 @ X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | (m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.20/0.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 0.20/0.55          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.55         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.55  thf(t51_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.55       ( A ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.55           = (X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.55         (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('37', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55         != (k2_subset_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('41', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.55  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d5_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X34 : $i, X35 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['43', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['42', '47'])).
% 0.20/0.55  thf('49', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['39', '48'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
