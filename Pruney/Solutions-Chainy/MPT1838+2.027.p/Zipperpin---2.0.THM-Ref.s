%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjJBs3i9KW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  350 ( 600 expanded)
%              Number of equality atoms :   49 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['6'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ~ ( v1_zfmisc_1 @ X22 )
      | ( X22
        = ( k6_domain_1 @ X22 @ ( sk_B @ X22 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('13',plain,(
    ! [X22: $i] :
      ( ~ ( v1_zfmisc_1 @ X22 )
      | ( m1_subset_1 @ ( sk_B @ X22 ) @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = X16 )
      | ( ( k1_tarski @ X17 )
       != ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
       != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['11','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjJBs3i9KW
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 99 iterations in 0.046s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(t1_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.52           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.52              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t83_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X11 : $i, X13 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf(t69_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.52          | ~ (r1_tarski @ X9 @ X10)
% 0.21/0.52          | (v1_xboole_0 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(d1_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.52         ( ?[B:$i]:
% 0.21/0.52           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (~ (v1_zfmisc_1 @ X22)
% 0.21/0.52          | ((X22) = (k6_domain_1 @ X22 @ (sk_B @ X22)))
% 0.21/0.52          | (v1_xboole_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (~ (v1_zfmisc_1 @ X22)
% 0.21/0.52          | (m1_subset_1 @ (sk_B @ X22) @ X22)
% 0.21/0.52          | (v1_xboole_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X20)
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ X20)
% 0.21/0.52          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.52          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.52          | (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.52          | (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  thf('17', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t12_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('19', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf(t44_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.52          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (((X15) = (k1_xboole_0))
% 0.21/0.52          | ((X16) = (k1_xboole_0))
% 0.21/0.52          | ((X15) = (X16))
% 0.21/0.52          | ((k1_tarski @ X17) != (k2_xboole_0 @ X15 @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_tarski @ X0) != (sk_B_1))
% 0.21/0.52          | ((sk_A) = (sk_B_1))
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, (((sk_A) != (sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_tarski @ X0) != (sk_B_1))
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) != (sk_B_1))
% 0.21/0.52          | (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.52          | ((sk_A) = (k1_xboole_0))
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((X0) != (sk_B_1))
% 0.21/0.52          | (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52          | ((sk_A) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.52          | (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('27', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.52      inference('simplify_reflect+', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('32', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '34'])).
% 0.21/0.52  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
