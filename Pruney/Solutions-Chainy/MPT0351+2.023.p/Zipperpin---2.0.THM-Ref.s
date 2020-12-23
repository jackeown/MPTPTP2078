%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VsP1zPkPN1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:00 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 153 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  539 (1467 expanded)
%              Number of equality atoms :   37 ( 109 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X25 ) @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','35'])).

thf('40',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['27','34'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VsP1zPkPN1
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:36:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.53/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.70  % Solved by: fo/fo7.sh
% 1.53/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.70  % done 2147 iterations in 1.250s
% 1.53/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.70  % SZS output start Refutation
% 1.53/1.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.53/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.53/1.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.53/1.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.53/1.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.53/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.53/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.70  thf(d3_xboole_0, axiom,
% 1.53/1.70    (![A:$i,B:$i,C:$i]:
% 1.53/1.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.53/1.70       ( ![D:$i]:
% 1.53/1.70         ( ( r2_hidden @ D @ C ) <=>
% 1.53/1.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.53/1.70  thf('0', plain,
% 1.53/1.70      (![X5 : $i, X7 : $i, X9 : $i]:
% 1.53/1.70         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X7)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.53/1.70  thf(t28_subset_1, conjecture,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.70       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 1.53/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.70    (~( ![A:$i,B:$i]:
% 1.53/1.70        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.70          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 1.53/1.70    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 1.53/1.70  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(d2_subset_1, axiom,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( ( v1_xboole_0 @ A ) =>
% 1.53/1.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.53/1.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.53/1.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.53/1.70  thf('2', plain,
% 1.53/1.70      (![X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X21 @ X22)
% 1.53/1.70          | (r2_hidden @ X21 @ X22)
% 1.53/1.70          | (v1_xboole_0 @ X22))),
% 1.53/1.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.53/1.70  thf('3', plain,
% 1.53/1.70      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.53/1.70        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.53/1.70  thf(fc1_subset_1, axiom,
% 1.53/1.70    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.53/1.70  thf('4', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 1.53/1.70      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.53/1.70  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.53/1.70      inference('clc', [status(thm)], ['3', '4'])).
% 1.53/1.70  thf(d1_zfmisc_1, axiom,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.53/1.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.53/1.70  thf('6', plain,
% 1.53/1.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X17 @ X16)
% 1.53/1.70          | (r1_tarski @ X17 @ X15)
% 1.53/1.70          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.53/1.70  thf('7', plain,
% 1.53/1.70      (![X15 : $i, X17 : $i]:
% 1.53/1.70         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['6'])).
% 1.53/1.70  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.53/1.70      inference('sup-', [status(thm)], ['5', '7'])).
% 1.53/1.70  thf(d3_tarski, axiom,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( r1_tarski @ A @ B ) <=>
% 1.53/1.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.53/1.70  thf('9', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X0 @ X1)
% 1.53/1.70          | (r2_hidden @ X0 @ X2)
% 1.53/1.70          | ~ (r1_tarski @ X1 @ X2))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.70  thf('10', plain,
% 1.53/1.70      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.53/1.70      inference('sup-', [status(thm)], ['8', '9'])).
% 1.53/1.70  thf('11', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ X1)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ X0)
% 1.53/1.70          | ((X1) = (k2_xboole_0 @ sk_B @ X0))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['0', '10'])).
% 1.53/1.70  thf('12', plain,
% 1.53/1.70      (![X5 : $i, X7 : $i, X9 : $i]:
% 1.53/1.70         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X7)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.53/1.70  thf('13', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('eq_fact', [status(thm)], ['12'])).
% 1.53/1.70  thf('14', plain,
% 1.53/1.70      (![X5 : $i, X7 : $i, X9 : $i]:
% 1.53/1.70         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.53/1.70  thf('15', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['13', '14'])).
% 1.53/1.70  thf('16', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['15'])).
% 1.53/1.70  thf('17', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('eq_fact', [status(thm)], ['12'])).
% 1.53/1.70  thf('18', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.53/1.70      inference('clc', [status(thm)], ['16', '17'])).
% 1.53/1.70  thf('19', plain,
% 1.53/1.70      (![X5 : $i, X7 : $i, X9 : $i]:
% 1.53/1.70         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X7)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.53/1.70  thf('20', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 1.53/1.70          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['18', '19'])).
% 1.53/1.70  thf('21', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 1.53/1.70          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['20'])).
% 1.53/1.70  thf('22', plain,
% 1.53/1.70      ((((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))
% 1.53/1.70        | (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 1.53/1.70        | (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 1.53/1.70        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['11', '21'])).
% 1.53/1.70  thf('23', plain,
% 1.53/1.70      (((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 1.53/1.70        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['22'])).
% 1.53/1.70  thf('24', plain,
% 1.53/1.70      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 1.53/1.70         != (k2_subset_1 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.53/1.70  thf('25', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.53/1.70  thf('26', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.53/1.70  thf('27', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 1.53/1.70      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.53/1.70  thf(dt_k2_subset_1, axiom,
% 1.53/1.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.53/1.70  thf('28', plain,
% 1.53/1.70      (![X25 : $i]: (m1_subset_1 @ (k2_subset_1 @ X25) @ (k1_zfmisc_1 @ X25))),
% 1.53/1.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.53/1.70  thf('29', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.53/1.70  thf('30', plain, (![X25 : $i]: (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X25))),
% 1.53/1.70      inference('demod', [status(thm)], ['28', '29'])).
% 1.53/1.70  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(redefinition_k4_subset_1, axiom,
% 1.53/1.70    (![A:$i,B:$i,C:$i]:
% 1.53/1.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.53/1.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.53/1.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.53/1.70  thf('32', plain,
% 1.53/1.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 1.53/1.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 1.53/1.70          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 1.53/1.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.53/1.70  thf('33', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['31', '32'])).
% 1.53/1.70  thf('34', plain,
% 1.53/1.70      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['30', '33'])).
% 1.53/1.70  thf('35', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 1.53/1.70      inference('demod', [status(thm)], ['27', '34'])).
% 1.53/1.70  thf('36', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)),
% 1.53/1.70      inference('simplify_reflect-', [status(thm)], ['23', '35'])).
% 1.53/1.70  thf('37', plain,
% 1.53/1.70      (![X5 : $i, X7 : $i, X9 : $i]:
% 1.53/1.70         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 1.53/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.53/1.70  thf('38', plain,
% 1.53/1.70      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 1.53/1.70        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['36', '37'])).
% 1.53/1.70  thf('39', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)),
% 1.53/1.70      inference('simplify_reflect-', [status(thm)], ['23', '35'])).
% 1.53/1.70  thf('40', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.53/1.70      inference('demod', [status(thm)], ['38', '39'])).
% 1.53/1.70  thf('41', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 1.53/1.70      inference('demod', [status(thm)], ['27', '34'])).
% 1.53/1.70  thf('42', plain, ($false),
% 1.53/1.70      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 1.53/1.70  
% 1.53/1.70  % SZS output end Refutation
% 1.53/1.70  
% 1.53/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
