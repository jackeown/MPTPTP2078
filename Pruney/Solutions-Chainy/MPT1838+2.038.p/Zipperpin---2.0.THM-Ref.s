%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WdotzqX4B8

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  280 ( 539 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ~ ( v1_zfmisc_1 @ X11 )
      | ( X11
        = ( k6_domain_1 @ X11 @ ( sk_B_1 @ X11 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v1_zfmisc_1 @ X11 )
      | ( m1_subset_1 @ ( sk_B_1 @ X11 ) @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k1_tarski @ X4 ) )
      | ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WdotzqX4B8
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.024s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(t1_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d1_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.48         ( ?[B:$i]:
% 0.21/0.48           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X11)
% 0.21/0.48          | ((X11) = (k6_domain_1 @ X11 @ (sk_B_1 @ X11)))
% 0.21/0.48          | (v1_xboole_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X11)
% 0.21/0.48          | (m1_subset_1 @ (sk_B_1 @ X11) @ X11)
% 0.21/0.48          | (v1_xboole_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ X9)
% 0.21/0.48          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf(l3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (((X5) = (k1_tarski @ X4))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X5 @ (k1_tarski @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.48  thf('13', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_A) = (sk_B_2))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['7', '16'])).
% 0.21/0.48  thf('18', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (((sk_A) != (sk_B_2))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('24', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('29', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '23', '28'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
