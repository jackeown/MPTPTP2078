%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKG3vq2b4d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 151 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  396 (1247 expanded)
%              Number of equality atoms :   32 ( 102 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ~ ( v1_zfmisc_1 @ X17 )
      | ( X17
        = ( k6_domain_1 @ X17 @ ( sk_B_1 @ X17 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('9',plain,(
    ! [X17: $i] :
      ( ~ ( v1_zfmisc_1 @ X17 )
      | ( m1_subset_1 @ ( sk_B_1 @ X17 ) @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_B_2 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B @ sk_A )
    = ( sk_B_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('24',plain,
    ( ( sk_B_2
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_2
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_2 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('42',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cKG3vq2b4d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:38:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 143 iterations in 0.103s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(t1_tex_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.55              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d1_xboole_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('2', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.55          | (r2_hidden @ X3 @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('7', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.21/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(d1_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.55         ( ?[B:$i]:
% 0.21/0.55           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X17 : $i]:
% 0.21/0.55         (~ (v1_zfmisc_1 @ X17)
% 0.21/0.55          | ((X17) = (k6_domain_1 @ X17 @ (sk_B_1 @ X17)))
% 0.21/0.55          | (v1_xboole_0 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X17 : $i]:
% 0.21/0.55         (~ (v1_zfmisc_1 @ X17)
% 0.21/0.55          | (m1_subset_1 @ (sk_B_1 @ X17) @ X17)
% 0.21/0.55          | (v1_xboole_0 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (m1_subset_1 @ X16 @ X15)
% 0.21/0.55          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X0)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.55          | (v1_xboole_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.55          | (v1_xboole_0 @ X0)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ X0)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ X0)
% 0.21/0.55          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.55  thf(d1_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.55          | ((X13) = (X10))
% 0.21/0.55          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X10 : $i, X13 : $i]:
% 0.21/0.55         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ X0)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | ((X1) = (sk_B_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      ((((sk_B @ sk_A) = (sk_B_1 @ sk_B_2))
% 0.21/0.55        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.55  thf('19', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((((sk_B @ sk_A) = (sk_B_1 @ sk_B_2)) | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('22', plain, (((sk_B @ sk_A) = (sk_B_1 @ sk_B_2))),
% 0.21/0.55      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ X0)
% 0.21/0.55          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.55        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((((sk_B_2) = (k1_tarski @ (sk_B @ sk_A))) | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('28', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X4 : $i, X6 : $i]:
% 0.21/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X10 : $i, X13 : $i]:
% 0.21/0.55         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.55          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X4 : $i, X6 : $i]:
% 0.21/0.55         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X7 : $i, X9 : $i]:
% 0.21/0.55         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X0)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.55          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ sk_B_2)
% 0.21/0.55        | ((sk_A) = (k1_tarski @ (sk_B @ sk_A)))
% 0.21/0.55        | (v1_xboole_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['28', '38'])).
% 0.21/0.55  thf('40', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('41', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('42', plain, ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.55  thf('43', plain, (((sk_A) != (sk_B_2))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
