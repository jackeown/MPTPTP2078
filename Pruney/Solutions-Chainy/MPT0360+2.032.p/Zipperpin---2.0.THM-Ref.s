%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YUN4JzIwkZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:45 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 149 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  464 (1018 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( r1_tarski @ X34 @ ( k3_subset_1 @ X35 @ X36 ) )
      | ~ ( r1_tarski @ X36 @ ( k3_subset_1 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X33: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('28',plain,(
    ! [X23: $i] :
      ( r1_tarski @ X23 @ ( k1_zfmisc_1 @ ( k3_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X26 @ X25 )
      | ~ ( r1_tarski @ ( k2_tarski @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( m1_subset_1 @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ X38 @ ( k3_subset_1 @ X37 @ X38 ) )
      | ( X38
        = ( k1_subset_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('45',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YUN4JzIwkZ
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.56/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.77  % Solved by: fo/fo7.sh
% 0.56/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.77  % done 893 iterations in 0.307s
% 0.56/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.77  % SZS output start Refutation
% 0.56/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.56/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.56/0.77  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.56/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.56/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.77  thf(t40_subset_1, conjecture,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.56/0.77         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.77        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77          ( ( ( r1_tarski @ B @ C ) & 
% 0.56/0.77              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.56/0.77            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.56/0.77    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.56/0.77  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(t35_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77       ( ![C:$i]:
% 0.56/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.56/0.77             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.56/0.77  thf('2', plain,
% 0.56/0.77      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.56/0.77          | (r1_tarski @ X34 @ (k3_subset_1 @ X35 @ X36))
% 0.56/0.77          | ~ (r1_tarski @ X36 @ (k3_subset_1 @ X35 @ X34))
% 0.56/0.77          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.56/0.77  thf('3', plain,
% 0.56/0.77      (![X0 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.77          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.56/0.77          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.77  thf('4', plain,
% 0.56/0.77      (((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.56/0.77        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['0', '3'])).
% 0.56/0.77  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(d2_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.56/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.56/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.56/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.77  thf('6', plain,
% 0.56/0.77      (![X29 : $i, X30 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X29 @ X30)
% 0.56/0.77          | (r2_hidden @ X29 @ X30)
% 0.56/0.77          | (v1_xboole_0 @ X30))),
% 0.56/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.56/0.77  thf('7', plain,
% 0.56/0.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.77        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.77  thf(fc1_subset_1, axiom,
% 0.56/0.77    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.56/0.77  thf('8', plain, (![X33 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.56/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.56/0.77  thf('9', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('clc', [status(thm)], ['7', '8'])).
% 0.56/0.77  thf(l49_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.56/0.77  thf('10', plain,
% 0.56/0.77      (![X19 : $i, X20 : $i]:
% 0.56/0.77         ((r1_tarski @ X19 @ (k3_tarski @ X20)) | ~ (r2_hidden @ X19 @ X20))),
% 0.56/0.77      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.56/0.77  thf('11', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.77  thf(t99_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.56/0.77  thf('12', plain, (![X28 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X28)) = (X28))),
% 0.56/0.77      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.56/0.77  thf('13', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.56/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.56/0.77  thf('14', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(t1_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.56/0.77       ( r1_tarski @ A @ C ) ))).
% 0.56/0.77  thf('15', plain,
% 0.56/0.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.77         (~ (r1_tarski @ X5 @ X6)
% 0.56/0.77          | ~ (r1_tarski @ X6 @ X7)
% 0.56/0.77          | (r1_tarski @ X5 @ X7))),
% 0.56/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.56/0.77  thf('16', plain,
% 0.56/0.77      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.56/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.77  thf('17', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.56/0.77      inference('sup-', [status(thm)], ['13', '16'])).
% 0.56/0.77  thf(t28_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.56/0.77  thf('18', plain,
% 0.56/0.77      (![X8 : $i, X9 : $i]:
% 0.56/0.77         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.56/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.56/0.77  thf('19', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.56/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.77  thf(t100_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.77  thf('20', plain,
% 0.56/0.77      (![X3 : $i, X4 : $i]:
% 0.56/0.77         ((k4_xboole_0 @ X3 @ X4)
% 0.56/0.77           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.77  thf('21', plain,
% 0.56/0.77      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.77  thf(t92_xboole_1, axiom,
% 0.56/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.56/0.77  thf('22', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.56/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.56/0.77  thf('23', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.56/0.77      inference('demod', [status(thm)], ['21', '22'])).
% 0.56/0.77  thf(t98_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.56/0.77  thf('24', plain,
% 0.56/0.77      (![X12 : $i, X13 : $i]:
% 0.56/0.77         ((k2_xboole_0 @ X12 @ X13)
% 0.56/0.77           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.56/0.77  thf('25', plain,
% 0.56/0.77      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.77  thf(t5_boole, axiom,
% 0.56/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.77  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.56/0.77      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.77  thf('27', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.56/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.77  thf(t100_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.56/0.77  thf('28', plain,
% 0.56/0.77      (![X23 : $i]: (r1_tarski @ X23 @ (k1_zfmisc_1 @ (k3_tarski @ X23)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.56/0.77  thf(t38_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.56/0.77       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.56/0.77  thf('29', plain,
% 0.56/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.56/0.77         ((r2_hidden @ X26 @ X25)
% 0.56/0.77          | ~ (r1_tarski @ (k2_tarski @ X24 @ X26) @ X25))),
% 0.56/0.77      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.56/0.77  thf('30', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.56/0.77  thf(l51_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.77  thf('31', plain,
% 0.56/0.77      (![X21 : $i, X22 : $i]:
% 0.56/0.77         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.56/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.56/0.77  thf('32', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.56/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.56/0.77  thf('33', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('sup+', [status(thm)], ['27', '32'])).
% 0.56/0.77  thf('34', plain,
% 0.56/0.77      (![X29 : $i, X30 : $i]:
% 0.56/0.77         (~ (r2_hidden @ X29 @ X30)
% 0.56/0.77          | (m1_subset_1 @ X29 @ X30)
% 0.56/0.77          | (v1_xboole_0 @ X30))),
% 0.56/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.56/0.77  thf(d1_xboole_0, axiom,
% 0.56/0.77    (![A:$i]:
% 0.56/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.77  thf('35', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.77  thf('36', plain,
% 0.56/0.77      (![X29 : $i, X30 : $i]:
% 0.56/0.77         ((m1_subset_1 @ X29 @ X30) | ~ (r2_hidden @ X29 @ X30))),
% 0.56/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.56/0.77  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('sup-', [status(thm)], ['33', '36'])).
% 0.56/0.77  thf('38', plain, ((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.56/0.77      inference('demod', [status(thm)], ['4', '37'])).
% 0.56/0.77  thf('39', plain,
% 0.56/0.77      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.56/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.77  thf('40', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.56/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.56/0.77  thf(t38_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.56/0.77         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.56/0.77  thf('41', plain,
% 0.56/0.77      (![X37 : $i, X38 : $i]:
% 0.56/0.77         (~ (r1_tarski @ X38 @ (k3_subset_1 @ X37 @ X38))
% 0.56/0.77          | ((X38) = (k1_subset_1 @ X37))
% 0.56/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.56/0.77  thf('42', plain,
% 0.56/0.77      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.77        | ((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.56/0.77  thf('43', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.77      inference('sup-', [status(thm)], ['33', '36'])).
% 0.56/0.77  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.56/0.77  thf('44', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.56/0.77      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.56/0.77  thf('45', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.56/0.77      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.56/0.77  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('47', plain, ($false),
% 0.56/0.77      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.56/0.77  
% 0.56/0.77  % SZS output end Refutation
% 0.56/0.77  
% 0.56/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
