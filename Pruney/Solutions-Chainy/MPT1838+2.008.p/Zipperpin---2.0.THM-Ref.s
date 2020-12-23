%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxbqVb4pAO

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 35.33s
% Output     : Refutation 35.33s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  321 ( 580 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X26 )
      | ( ( k4_xboole_0 @ X24 @ X26 )
       != X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','8'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( X32
        = ( k6_domain_1 @ X32 @ ( sk_B @ X32 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('11',plain,(
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( m1_subset_1 @ ( sk_B @ X32 ) @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['9','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxbqVb4pAO
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 35.33/35.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 35.33/35.56  % Solved by: fo/fo7.sh
% 35.33/35.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.33/35.56  % done 26182 iterations in 35.077s
% 35.33/35.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 35.33/35.56  % SZS output start Refutation
% 35.33/35.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 35.33/35.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 35.33/35.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.33/35.56  thf(sk_B_type, type, sk_B: $i > $i).
% 35.33/35.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 35.33/35.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.33/35.56  thf(sk_A_type, type, sk_A: $i).
% 35.33/35.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 35.33/35.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 35.33/35.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 35.33/35.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 35.33/35.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 35.33/35.56  thf(t1_tex_2, conjecture,
% 35.33/35.56    (![A:$i]:
% 35.33/35.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 35.33/35.56       ( ![B:$i]:
% 35.33/35.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 35.33/35.56           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 35.33/35.56  thf(zf_stmt_0, negated_conjecture,
% 35.33/35.56    (~( ![A:$i]:
% 35.33/35.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 35.33/35.56          ( ![B:$i]:
% 35.33/35.56            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 35.33/35.56              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 35.33/35.56    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 35.33/35.56  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf(d10_xboole_0, axiom,
% 35.33/35.56    (![A:$i,B:$i]:
% 35.33/35.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 35.33/35.56  thf('1', plain,
% 35.33/35.56      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 35.33/35.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 35.33/35.56  thf('2', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 35.33/35.56      inference('simplify', [status(thm)], ['1'])).
% 35.33/35.56  thf(t3_boole, axiom,
% 35.33/35.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 35.33/35.56  thf('3', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 35.33/35.56      inference('cnf', [status(esa)], [t3_boole])).
% 35.33/35.56  thf(t83_xboole_1, axiom,
% 35.33/35.56    (![A:$i,B:$i]:
% 35.33/35.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 35.33/35.56  thf('4', plain,
% 35.33/35.56      (![X24 : $i, X26 : $i]:
% 35.33/35.56         ((r1_xboole_0 @ X24 @ X26) | ((k4_xboole_0 @ X24 @ X26) != (X24)))),
% 35.33/35.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 35.33/35.56  thf('5', plain,
% 35.33/35.56      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 35.33/35.56      inference('sup-', [status(thm)], ['3', '4'])).
% 35.33/35.56  thf('6', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 35.33/35.56      inference('simplify', [status(thm)], ['5'])).
% 35.33/35.56  thf(t69_xboole_1, axiom,
% 35.33/35.56    (![A:$i,B:$i]:
% 35.33/35.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 35.33/35.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 35.33/35.56  thf('7', plain,
% 35.33/35.56      (![X22 : $i, X23 : $i]:
% 35.33/35.56         (~ (r1_xboole_0 @ X22 @ X23)
% 35.33/35.56          | ~ (r1_tarski @ X22 @ X23)
% 35.33/35.56          | (v1_xboole_0 @ X22))),
% 35.33/35.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 35.33/35.56  thf('8', plain,
% 35.33/35.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 35.33/35.56      inference('sup-', [status(thm)], ['6', '7'])).
% 35.33/35.56  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 35.33/35.56      inference('sup-', [status(thm)], ['2', '8'])).
% 35.33/35.56  thf(d1_tex_2, axiom,
% 35.33/35.56    (![A:$i]:
% 35.33/35.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 35.33/35.56       ( ( v1_zfmisc_1 @ A ) <=>
% 35.33/35.56         ( ?[B:$i]:
% 35.33/35.56           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 35.33/35.56  thf('10', plain,
% 35.33/35.56      (![X32 : $i]:
% 35.33/35.56         (~ (v1_zfmisc_1 @ X32)
% 35.33/35.56          | ((X32) = (k6_domain_1 @ X32 @ (sk_B @ X32)))
% 35.33/35.56          | (v1_xboole_0 @ X32))),
% 35.33/35.56      inference('cnf', [status(esa)], [d1_tex_2])).
% 35.33/35.56  thf('11', plain,
% 35.33/35.56      (![X32 : $i]:
% 35.33/35.56         (~ (v1_zfmisc_1 @ X32)
% 35.33/35.56          | (m1_subset_1 @ (sk_B @ X32) @ X32)
% 35.33/35.56          | (v1_xboole_0 @ X32))),
% 35.33/35.56      inference('cnf', [status(esa)], [d1_tex_2])).
% 35.33/35.56  thf(redefinition_k6_domain_1, axiom,
% 35.33/35.56    (![A:$i,B:$i]:
% 35.33/35.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 35.33/35.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 35.33/35.56  thf('12', plain,
% 35.33/35.56      (![X30 : $i, X31 : $i]:
% 35.33/35.56         ((v1_xboole_0 @ X30)
% 35.33/35.56          | ~ (m1_subset_1 @ X31 @ X30)
% 35.33/35.56          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 35.33/35.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 35.33/35.56  thf('13', plain,
% 35.33/35.56      (![X0 : $i]:
% 35.33/35.56         ((v1_xboole_0 @ X0)
% 35.33/35.56          | ~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 35.33/35.56          | (v1_xboole_0 @ X0))),
% 35.33/35.56      inference('sup-', [status(thm)], ['11', '12'])).
% 35.33/35.56  thf('14', plain,
% 35.33/35.56      (![X0 : $i]:
% 35.33/35.56         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 35.33/35.56          | ~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | (v1_xboole_0 @ X0))),
% 35.33/35.56      inference('simplify', [status(thm)], ['13'])).
% 35.33/35.56  thf('15', plain,
% 35.33/35.56      (![X0 : $i]:
% 35.33/35.56         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 35.33/35.56          | (v1_xboole_0 @ X0)
% 35.33/35.56          | ~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | (v1_xboole_0 @ X0)
% 35.33/35.56          | ~ (v1_zfmisc_1 @ X0))),
% 35.33/35.56      inference('sup+', [status(thm)], ['10', '14'])).
% 35.33/35.56  thf('16', plain,
% 35.33/35.56      (![X0 : $i]:
% 35.33/35.56         (~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | (v1_xboole_0 @ X0)
% 35.33/35.56          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 35.33/35.56      inference('simplify', [status(thm)], ['15'])).
% 35.33/35.56  thf('17', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('18', plain,
% 35.33/35.56      (![X0 : $i]:
% 35.33/35.56         (~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | (v1_xboole_0 @ X0)
% 35.33/35.56          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 35.33/35.56      inference('simplify', [status(thm)], ['15'])).
% 35.33/35.56  thf(l3_zfmisc_1, axiom,
% 35.33/35.56    (![A:$i,B:$i]:
% 35.33/35.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 35.33/35.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 35.33/35.56  thf('19', plain,
% 35.33/35.56      (![X27 : $i, X28 : $i]:
% 35.33/35.56         (((X28) = (k1_tarski @ X27))
% 35.33/35.56          | ((X28) = (k1_xboole_0))
% 35.33/35.56          | ~ (r1_tarski @ X28 @ (k1_tarski @ X27)))),
% 35.33/35.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 35.33/35.56  thf('20', plain,
% 35.33/35.56      (![X0 : $i, X1 : $i]:
% 35.33/35.56         (~ (r1_tarski @ X1 @ X0)
% 35.33/35.56          | (v1_xboole_0 @ X0)
% 35.33/35.56          | ~ (v1_zfmisc_1 @ X0)
% 35.33/35.56          | ((X1) = (k1_xboole_0))
% 35.33/35.56          | ((X1) = (k1_tarski @ (sk_B @ X0))))),
% 35.33/35.56      inference('sup-', [status(thm)], ['18', '19'])).
% 35.33/35.56  thf('21', plain,
% 35.33/35.56      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 35.33/35.56        | ((sk_A) = (k1_xboole_0))
% 35.33/35.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 35.33/35.56        | (v1_xboole_0 @ sk_B_1))),
% 35.33/35.56      inference('sup-', [status(thm)], ['17', '20'])).
% 35.33/35.56  thf('22', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('23', plain,
% 35.33/35.56      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 35.33/35.56        | ((sk_A) = (k1_xboole_0))
% 35.33/35.56        | (v1_xboole_0 @ sk_B_1))),
% 35.33/35.56      inference('demod', [status(thm)], ['21', '22'])).
% 35.33/35.56  thf('24', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('25', plain,
% 35.33/35.56      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 35.33/35.56      inference('clc', [status(thm)], ['23', '24'])).
% 35.33/35.56  thf('26', plain,
% 35.33/35.56      ((((sk_A) = (sk_B_1))
% 35.33/35.56        | (v1_xboole_0 @ sk_B_1)
% 35.33/35.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 35.33/35.56        | ((sk_A) = (k1_xboole_0)))),
% 35.33/35.56      inference('sup+', [status(thm)], ['16', '25'])).
% 35.33/35.56  thf('27', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('28', plain,
% 35.33/35.56      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 35.33/35.56      inference('demod', [status(thm)], ['26', '27'])).
% 35.33/35.56  thf('29', plain, (((sk_A) != (sk_B_1))),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('30', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 35.33/35.56      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 35.33/35.56  thf('31', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 35.33/35.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.33/35.56  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 35.33/35.56      inference('clc', [status(thm)], ['30', '31'])).
% 35.33/35.56  thf('33', plain, ((v1_xboole_0 @ sk_A)),
% 35.33/35.56      inference('demod', [status(thm)], ['9', '32'])).
% 35.33/35.56  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 35.33/35.56  
% 35.33/35.56  % SZS output end Refutation
% 35.33/35.56  
% 35.33/35.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
