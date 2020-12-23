%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NzWDzxDL9b

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  299 ( 466 expanded)
%              Number of equality atoms :   40 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( r1_tarski @ k1_xboole_0 @ X23 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X40: $i] :
      ( ~ ( v1_zfmisc_1 @ X40 )
      | ( X40
        = ( k6_domain_1 @ X40 @ ( sk_B_1 @ X40 ) ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('7',plain,(
    ! [X40: $i] :
      ( ~ ( v1_zfmisc_1 @ X40 )
      | ( m1_subset_1 @ ( sk_B_1 @ X40 ) @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( ( k6_domain_1 @ X38 @ X39 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = X32 )
      | ( ( k1_tarski @ X33 )
       != ( k2_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['5','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NzWDzxDL9b
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.31/3.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.31/3.49  % Solved by: fo/fo7.sh
% 3.31/3.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.31/3.49  % done 7091 iterations in 3.051s
% 3.31/3.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.31/3.49  % SZS output start Refutation
% 3.31/3.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.31/3.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.31/3.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.31/3.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.31/3.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.31/3.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 3.31/3.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.31/3.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 3.31/3.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.31/3.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.31/3.49  thf(sk_A_type, type, sk_A: $i).
% 3.31/3.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.31/3.49  thf(sk_B_type, type, sk_B: $i > $i).
% 3.31/3.49  thf(t1_tex_2, conjecture,
% 3.31/3.49    (![A:$i]:
% 3.31/3.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.31/3.49       ( ![B:$i]:
% 3.31/3.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 3.31/3.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 3.31/3.49  thf(zf_stmt_0, negated_conjecture,
% 3.31/3.49    (~( ![A:$i]:
% 3.31/3.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.31/3.49          ( ![B:$i]:
% 3.31/3.49            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 3.31/3.49              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 3.31/3.49    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 3.31/3.49  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.31/3.49  thf('1', plain, (![X23 : $i]: (r1_tarski @ k1_xboole_0 @ X23)),
% 3.31/3.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.31/3.49  thf(d1_xboole_0, axiom,
% 3.31/3.49    (![A:$i]:
% 3.31/3.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.31/3.49  thf('2', plain,
% 3.31/3.49      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 3.31/3.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.31/3.49  thf(t7_ordinal1, axiom,
% 3.31/3.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.31/3.49  thf('3', plain,
% 3.31/3.49      (![X36 : $i, X37 : $i]:
% 3.31/3.49         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 3.31/3.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.31/3.49  thf('4', plain,
% 3.31/3.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.31/3.49      inference('sup-', [status(thm)], ['2', '3'])).
% 3.31/3.49  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.31/3.49      inference('sup-', [status(thm)], ['1', '4'])).
% 3.31/3.49  thf(d1_tex_2, axiom,
% 3.31/3.49    (![A:$i]:
% 3.31/3.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.31/3.49       ( ( v1_zfmisc_1 @ A ) <=>
% 3.31/3.49         ( ?[B:$i]:
% 3.31/3.49           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 3.31/3.49  thf('6', plain,
% 3.31/3.49      (![X40 : $i]:
% 3.31/3.49         (~ (v1_zfmisc_1 @ X40)
% 3.31/3.49          | ((X40) = (k6_domain_1 @ X40 @ (sk_B_1 @ X40)))
% 3.31/3.49          | (v1_xboole_0 @ X40))),
% 3.31/3.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 3.31/3.49  thf('7', plain,
% 3.31/3.49      (![X40 : $i]:
% 3.31/3.49         (~ (v1_zfmisc_1 @ X40)
% 3.31/3.49          | (m1_subset_1 @ (sk_B_1 @ X40) @ X40)
% 3.31/3.49          | (v1_xboole_0 @ X40))),
% 3.31/3.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 3.31/3.49  thf(redefinition_k6_domain_1, axiom,
% 3.31/3.49    (![A:$i,B:$i]:
% 3.31/3.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 3.31/3.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 3.31/3.49  thf('8', plain,
% 3.31/3.49      (![X38 : $i, X39 : $i]:
% 3.31/3.49         ((v1_xboole_0 @ X38)
% 3.31/3.49          | ~ (m1_subset_1 @ X39 @ X38)
% 3.31/3.49          | ((k6_domain_1 @ X38 @ X39) = (k1_tarski @ X39)))),
% 3.31/3.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 3.31/3.49  thf('9', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         ((v1_xboole_0 @ X0)
% 3.31/3.49          | ~ (v1_zfmisc_1 @ X0)
% 3.31/3.49          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 3.31/3.49          | (v1_xboole_0 @ X0))),
% 3.31/3.49      inference('sup-', [status(thm)], ['7', '8'])).
% 3.31/3.49  thf('10', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 3.31/3.49          | ~ (v1_zfmisc_1 @ X0)
% 3.31/3.49          | (v1_xboole_0 @ X0))),
% 3.31/3.49      inference('simplify', [status(thm)], ['9'])).
% 3.31/3.49  thf('11', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 3.31/3.49          | (v1_xboole_0 @ X0)
% 3.31/3.49          | ~ (v1_zfmisc_1 @ X0)
% 3.31/3.49          | (v1_xboole_0 @ X0)
% 3.31/3.49          | ~ (v1_zfmisc_1 @ X0))),
% 3.31/3.49      inference('sup+', [status(thm)], ['6', '10'])).
% 3.31/3.49  thf('12', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (~ (v1_zfmisc_1 @ X0)
% 3.31/3.49          | (v1_xboole_0 @ X0)
% 3.31/3.49          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 3.31/3.49      inference('simplify', [status(thm)], ['11'])).
% 3.31/3.49  thf('13', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf(t12_xboole_1, axiom,
% 3.31/3.49    (![A:$i,B:$i]:
% 3.31/3.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.31/3.49  thf('14', plain,
% 3.31/3.49      (![X17 : $i, X18 : $i]:
% 3.31/3.49         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 3.31/3.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.31/3.49  thf('15', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 3.31/3.49      inference('sup-', [status(thm)], ['13', '14'])).
% 3.31/3.49  thf(t44_zfmisc_1, axiom,
% 3.31/3.49    (![A:$i,B:$i,C:$i]:
% 3.31/3.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.31/3.49          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.31/3.49          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 3.31/3.49  thf('16', plain,
% 3.31/3.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.31/3.49         (((X31) = (k1_xboole_0))
% 3.31/3.49          | ((X32) = (k1_xboole_0))
% 3.31/3.49          | ((X31) = (X32))
% 3.31/3.49          | ((k1_tarski @ X33) != (k2_xboole_0 @ X31 @ X32)))),
% 3.31/3.49      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 3.31/3.49  thf('17', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (((k1_tarski @ X0) != (sk_B_2))
% 3.31/3.49          | ((sk_A) = (sk_B_2))
% 3.31/3.49          | ((sk_B_2) = (k1_xboole_0))
% 3.31/3.49          | ((sk_A) = (k1_xboole_0)))),
% 3.31/3.49      inference('sup-', [status(thm)], ['15', '16'])).
% 3.31/3.49  thf('18', plain, (((sk_A) != (sk_B_2))),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf('19', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (((k1_tarski @ X0) != (sk_B_2))
% 3.31/3.49          | ((sk_B_2) = (k1_xboole_0))
% 3.31/3.49          | ((sk_A) = (k1_xboole_0)))),
% 3.31/3.49      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 3.31/3.49  thf('20', plain,
% 3.31/3.49      (![X0 : $i]:
% 3.31/3.49         (((X0) != (sk_B_2))
% 3.31/3.49          | (v1_xboole_0 @ X0)
% 3.31/3.49          | ~ (v1_zfmisc_1 @ X0)
% 3.31/3.49          | ((sk_A) = (k1_xboole_0))
% 3.31/3.49          | ((sk_B_2) = (k1_xboole_0)))),
% 3.31/3.49      inference('sup-', [status(thm)], ['12', '19'])).
% 3.31/3.49  thf('21', plain,
% 3.31/3.49      ((((sk_B_2) = (k1_xboole_0))
% 3.31/3.49        | ((sk_A) = (k1_xboole_0))
% 3.31/3.49        | ~ (v1_zfmisc_1 @ sk_B_2)
% 3.31/3.49        | (v1_xboole_0 @ sk_B_2))),
% 3.31/3.49      inference('simplify', [status(thm)], ['20'])).
% 3.31/3.49  thf('22', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf('23', plain,
% 3.31/3.49      ((((sk_B_2) = (k1_xboole_0))
% 3.31/3.49        | ((sk_A) = (k1_xboole_0))
% 3.31/3.49        | (v1_xboole_0 @ sk_B_2))),
% 3.31/3.49      inference('simplify_reflect+', [status(thm)], ['21', '22'])).
% 3.31/3.49  thf('24', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf('25', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 3.31/3.49      inference('clc', [status(thm)], ['23', '24'])).
% 3.31/3.49  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.31/3.49      inference('sup-', [status(thm)], ['1', '4'])).
% 3.31/3.49  thf('27', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 3.31/3.49      inference('sup+', [status(thm)], ['25', '26'])).
% 3.31/3.49  thf('28', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 3.31/3.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.49  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 3.31/3.49      inference('clc', [status(thm)], ['27', '28'])).
% 3.31/3.49  thf('30', plain, ((v1_xboole_0 @ sk_A)),
% 3.31/3.49      inference('demod', [status(thm)], ['5', '29'])).
% 3.31/3.49  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 3.31/3.49  
% 3.31/3.49  % SZS output end Refutation
% 3.31/3.49  
% 3.34/3.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
