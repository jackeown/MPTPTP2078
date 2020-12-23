%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FiimeNSylM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 165 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  552 (1233 expanded)
%              Number of equality atoms :   47 ( 110 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('8',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('13',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','14','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('23',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['32','58'])).

thf('60',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['5','14'])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FiimeNSylM
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 146 iterations in 0.051s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.19/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.49  thf(t38_subset_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.19/0.49        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.19/0.49        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.19/0.49       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['4'])).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('6', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('7', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['4'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('16', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['5', '14', '15'])).
% 0.19/0.49  thf('17', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['3', '16'])).
% 0.19/0.49  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d5_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['17', '20'])).
% 0.19/0.49  thf(t106_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X7 @ X9)
% 0.19/0.49          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.19/0.49  thf('23', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf(t86_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.19/0.49       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X12 @ X13)
% 0.19/0.49          | ~ (r1_xboole_0 @ X12 @ X14)
% 0.19/0.49          | (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))
% 0.19/0.49          | ~ (r1_tarski @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X2 : $i, X4 : $i]:
% 0.19/0.49         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_B)
% 0.19/0.49        | ((k4_xboole_0 @ sk_B @ sk_B) = (sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.19/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '31'])).
% 0.19/0.49  thf('33', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf(d1_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X15 @ X16)
% 0.19/0.49          | (r2_hidden @ X15 @ X17)
% 0.19/0.49          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i]:
% 0.19/0.49         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 0.19/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.19/0.49  thf(d2_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X20 @ X21)
% 0.19/0.49          | (m1_subset_1 @ X20 @ X21)
% 0.19/0.49          | (v1_xboole_0 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.19/0.49          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf(fc1_subset_1, axiom,
% 0.19/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.49  thf('39', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X29 : $i, X30 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 0.19/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.19/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf(t3_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('46', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.49  thf('47', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.49  thf('48', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['42', '47'])).
% 0.19/0.49  thf('49', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.19/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i]:
% 0.19/0.49         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 0.19/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.49  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X20 @ X21)
% 0.19/0.49          | (m1_subset_1 @ X20 @ X21)
% 0.19/0.49          | (v1_xboole_0 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.19/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf('54', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.49  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.49  thf('58', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['48', '57'])).
% 0.19/0.49  thf('59', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '58'])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.19/0.49         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['4'])).
% 0.19/0.49  thf('61', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.49  thf('63', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['5', '14'])).
% 0.19/0.49  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.19/0.49  thf('65', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
