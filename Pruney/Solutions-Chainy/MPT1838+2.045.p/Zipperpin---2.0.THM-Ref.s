%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hRsQ5xaofR

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  94 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  390 ( 612 expanded)
%              Number of equality atoms :   54 (  72 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ~ ( v1_zfmisc_1 @ X22 )
      | ( X22
        = ( k6_domain_1 @ X22 @ ( sk_B @ X22 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X4 @ X3 ) )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = X16 )
      | ( ( k1_tarski @ X17 )
       != ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = X16 )
      | ( ( k1_tarski @ X17 )
       != ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['10','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hRsQ5xaofR
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 58 iterations in 0.034s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(t1_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.54           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.54              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.54  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('1', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf(l32_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t83_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X9 : $i, X11 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf(t69_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (r1_xboole_0 @ X7 @ X8)
% 0.21/0.54          | ~ (r1_tarski @ X7 @ X8)
% 0.21/0.54          | (v1_xboole_0 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(d1_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.54         ( ?[B:$i]:
% 0.21/0.54           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X22)
% 0.21/0.54          | ((X22) = (k6_domain_1 @ X22 @ (sk_B @ X22)))
% 0.21/0.54          | (v1_xboole_0 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X22)
% 0.21/0.54          | (m1_subset_1 @ (sk_B @ X22) @ X22)
% 0.21/0.54          | (v1_xboole_0 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ X20)
% 0.21/0.54          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.54  thf('18', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t12_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.54  thf(l51_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (((k3_tarski @ (k2_tarski @ X4 @ X3)) = (X3))
% 0.21/0.54          | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.54  thf(t44_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.54          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (((X15) = (k1_xboole_0))
% 0.21/0.54          | ((X16) = (k1_xboole_0))
% 0.21/0.54          | ((X15) = (X16))
% 0.21/0.54          | ((k1_tarski @ X17) != (k2_xboole_0 @ X15 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (((X15) = (k1_xboole_0))
% 0.21/0.54          | ((X16) = (k1_xboole_0))
% 0.21/0.54          | ((X15) = (X16))
% 0.21/0.54          | ((k1_tarski @ X17) != (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_tarski @ X0) != (sk_B_1))
% 0.21/0.54          | ((sk_A) = (sk_B_1))
% 0.21/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.54  thf('27', plain, (((sk_A) != (sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_tarski @ X0) != (sk_B_1))
% 0.21/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((X0) != (sk_B_1))
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | ((sk_A) = (k1_xboole_0))
% 0.21/0.54          | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('31', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0))
% 0.21/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.54      inference('simplify_reflect+', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('36', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '38'])).
% 0.21/0.54  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
