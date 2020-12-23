%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0iKNHngbLg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:15 EST 2020

% Result     : Timeout 59.92s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  349 ( 608 expanded)
%              Number of equality atoms :   36 (  57 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_1 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_xboole_0 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k2_xboole_0 @ X12 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0iKNHngbLg
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 59.92/60.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 59.92/60.11  % Solved by: fo/fo7.sh
% 59.92/60.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.92/60.11  % done 31977 iterations in 59.659s
% 59.92/60.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 59.92/60.11  % SZS output start Refutation
% 59.92/60.11  thf(sk_A_type, type, sk_A: $i).
% 59.92/60.11  thf(sk_B_2_type, type, sk_B_2: $i).
% 59.92/60.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 59.92/60.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.92/60.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 59.92/60.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 59.92/60.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 59.92/60.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 59.92/60.11  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 59.92/60.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 59.92/60.11  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 59.92/60.11  thf(sk_B_type, type, sk_B: $i > $i).
% 59.92/60.11  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 59.92/60.11  thf(t1_tex_2, conjecture,
% 59.92/60.11    (![A:$i]:
% 59.92/60.11     ( ( ~( v1_xboole_0 @ A ) ) =>
% 59.92/60.11       ( ![B:$i]:
% 59.92/60.11         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 59.92/60.11           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 59.92/60.11  thf(zf_stmt_0, negated_conjecture,
% 59.92/60.11    (~( ![A:$i]:
% 59.92/60.11        ( ( ~( v1_xboole_0 @ A ) ) =>
% 59.92/60.11          ( ![B:$i]:
% 59.92/60.11            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 59.92/60.11              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 59.92/60.11    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 59.92/60.11  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf(d1_tex_2, axiom,
% 59.92/60.11    (![A:$i]:
% 59.92/60.11     ( ( ~( v1_xboole_0 @ A ) ) =>
% 59.92/60.11       ( ( v1_zfmisc_1 @ A ) <=>
% 59.92/60.11         ( ?[B:$i]:
% 59.92/60.11           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 59.92/60.11  thf('1', plain,
% 59.92/60.11      (![X28 : $i]:
% 59.92/60.11         (~ (v1_zfmisc_1 @ X28)
% 59.92/60.11          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_1 @ X28)))
% 59.92/60.11          | (v1_xboole_0 @ X28))),
% 59.92/60.11      inference('cnf', [status(esa)], [d1_tex_2])).
% 59.92/60.11  thf('2', plain,
% 59.92/60.11      (![X28 : $i]:
% 59.92/60.11         (~ (v1_zfmisc_1 @ X28)
% 59.92/60.11          | (m1_subset_1 @ (sk_B_1 @ X28) @ X28)
% 59.92/60.11          | (v1_xboole_0 @ X28))),
% 59.92/60.11      inference('cnf', [status(esa)], [d1_tex_2])).
% 59.92/60.11  thf(redefinition_k6_domain_1, axiom,
% 59.92/60.11    (![A:$i,B:$i]:
% 59.92/60.11     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 59.92/60.11       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 59.92/60.11  thf('3', plain,
% 59.92/60.11      (![X26 : $i, X27 : $i]:
% 59.92/60.11         ((v1_xboole_0 @ X26)
% 59.92/60.11          | ~ (m1_subset_1 @ X27 @ X26)
% 59.92/60.11          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 59.92/60.11      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 59.92/60.11  thf('4', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         ((v1_xboole_0 @ X0)
% 59.92/60.11          | ~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 59.92/60.11          | (v1_xboole_0 @ X0))),
% 59.92/60.11      inference('sup-', [status(thm)], ['2', '3'])).
% 59.92/60.11  thf('5', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 59.92/60.11          | ~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | (v1_xboole_0 @ X0))),
% 59.92/60.11      inference('simplify', [status(thm)], ['4'])).
% 59.92/60.11  thf('6', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 59.92/60.11          | (v1_xboole_0 @ X0)
% 59.92/60.11          | ~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | (v1_xboole_0 @ X0)
% 59.92/60.11          | ~ (v1_zfmisc_1 @ X0))),
% 59.92/60.11      inference('sup+', [status(thm)], ['1', '5'])).
% 59.92/60.11  thf('7', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         (~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | (v1_xboole_0 @ X0)
% 59.92/60.11          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 59.92/60.11      inference('simplify', [status(thm)], ['6'])).
% 59.92/60.11  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('9', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         (~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | (v1_xboole_0 @ X0)
% 59.92/60.11          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 59.92/60.11      inference('simplify', [status(thm)], ['6'])).
% 59.92/60.11  thf(l3_zfmisc_1, axiom,
% 59.92/60.11    (![A:$i,B:$i]:
% 59.92/60.11     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 59.92/60.11       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 59.92/60.11  thf('10', plain,
% 59.92/60.11      (![X21 : $i, X22 : $i]:
% 59.92/60.11         (((X22) = (k1_tarski @ X21))
% 59.92/60.11          | ((X22) = (k1_xboole_0))
% 59.92/60.11          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 59.92/60.11      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 59.92/60.11  thf('11', plain,
% 59.92/60.11      (![X0 : $i, X1 : $i]:
% 59.92/60.11         (~ (r1_tarski @ X1 @ X0)
% 59.92/60.11          | (v1_xboole_0 @ X0)
% 59.92/60.11          | ~ (v1_zfmisc_1 @ X0)
% 59.92/60.11          | ((X1) = (k1_xboole_0))
% 59.92/60.11          | ((X1) = (k1_tarski @ (sk_B_1 @ X0))))),
% 59.92/60.11      inference('sup-', [status(thm)], ['9', '10'])).
% 59.92/60.11  thf('12', plain,
% 59.92/60.11      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 59.92/60.11        | ((sk_A) = (k1_xboole_0))
% 59.92/60.11        | ~ (v1_zfmisc_1 @ sk_B_2)
% 59.92/60.11        | (v1_xboole_0 @ sk_B_2))),
% 59.92/60.11      inference('sup-', [status(thm)], ['8', '11'])).
% 59.92/60.11  thf('13', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('14', plain,
% 59.92/60.11      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 59.92/60.11        | ((sk_A) = (k1_xboole_0))
% 59.92/60.11        | (v1_xboole_0 @ sk_B_2))),
% 59.92/60.11      inference('demod', [status(thm)], ['12', '13'])).
% 59.92/60.11  thf('15', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('16', plain,
% 59.92/60.11      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 59.92/60.11      inference('clc', [status(thm)], ['14', '15'])).
% 59.92/60.11  thf('17', plain,
% 59.92/60.11      ((((sk_A) = (sk_B_2))
% 59.92/60.11        | (v1_xboole_0 @ sk_B_2)
% 59.92/60.11        | ~ (v1_zfmisc_1 @ sk_B_2)
% 59.92/60.11        | ((sk_A) = (k1_xboole_0)))),
% 59.92/60.11      inference('sup+', [status(thm)], ['7', '16'])).
% 59.92/60.11  thf('18', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('19', plain,
% 59.92/60.11      ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 59.92/60.11      inference('demod', [status(thm)], ['17', '18'])).
% 59.92/60.11  thf('20', plain, (((sk_A) != (sk_B_2))),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('21', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 59.92/60.11      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 59.92/60.11  thf('22', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 59.92/60.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.92/60.11  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 59.92/60.11      inference('clc', [status(thm)], ['21', '22'])).
% 59.92/60.11  thf(d10_xboole_0, axiom,
% 59.92/60.11    (![A:$i,B:$i]:
% 59.92/60.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 59.92/60.11  thf('24', plain,
% 59.92/60.11      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 59.92/60.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.92/60.11  thf('25', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 59.92/60.11      inference('simplify', [status(thm)], ['24'])).
% 59.92/60.11  thf(t1_boole, axiom,
% 59.92/60.11    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 59.92/60.11  thf('26', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 59.92/60.11      inference('cnf', [status(esa)], [t1_boole])).
% 59.92/60.11  thf(d1_xboole_0, axiom,
% 59.92/60.11    (![A:$i]:
% 59.92/60.11     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 59.92/60.11  thf('27', plain,
% 59.92/60.11      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 59.92/60.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 59.92/60.11  thf(d3_xboole_0, axiom,
% 59.92/60.11    (![A:$i,B:$i,C:$i]:
% 59.92/60.11     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 59.92/60.11       ( ![D:$i]:
% 59.92/60.11         ( ( r2_hidden @ D @ C ) <=>
% 59.92/60.11           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 59.92/60.11  thf('28', plain,
% 59.92/60.11      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 59.92/60.11         (~ (r2_hidden @ X9 @ X10)
% 59.92/60.11          | (r2_hidden @ X9 @ X11)
% 59.92/60.11          | ((X11) != (k2_xboole_0 @ X12 @ X10)))),
% 59.92/60.11      inference('cnf', [status(esa)], [d3_xboole_0])).
% 59.92/60.11  thf('29', plain,
% 59.92/60.11      (![X9 : $i, X10 : $i, X12 : $i]:
% 59.92/60.11         ((r2_hidden @ X9 @ (k2_xboole_0 @ X12 @ X10))
% 59.92/60.11          | ~ (r2_hidden @ X9 @ X10))),
% 59.92/60.11      inference('simplify', [status(thm)], ['28'])).
% 59.92/60.11  thf('30', plain,
% 59.92/60.11      (![X0 : $i, X1 : $i]:
% 59.92/60.11         ((v1_xboole_0 @ X0)
% 59.92/60.11          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 59.92/60.11      inference('sup-', [status(thm)], ['27', '29'])).
% 59.92/60.11  thf('31', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         ((r2_hidden @ (sk_B @ k1_xboole_0) @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 59.92/60.11      inference('sup+', [status(thm)], ['26', '30'])).
% 59.92/60.11  thf(t7_ordinal1, axiom,
% 59.92/60.11    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 59.92/60.11  thf('32', plain,
% 59.92/60.11      (![X24 : $i, X25 : $i]:
% 59.92/60.11         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 59.92/60.11      inference('cnf', [status(esa)], [t7_ordinal1])).
% 59.92/60.11  thf('33', plain,
% 59.92/60.11      (![X0 : $i]:
% 59.92/60.11         ((v1_xboole_0 @ k1_xboole_0)
% 59.92/60.11          | ~ (r1_tarski @ X0 @ (sk_B @ k1_xboole_0)))),
% 59.92/60.11      inference('sup-', [status(thm)], ['31', '32'])).
% 59.92/60.11  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 59.92/60.11      inference('sup-', [status(thm)], ['25', '33'])).
% 59.92/60.11  thf('35', plain, ($false),
% 59.92/60.11      inference('demod', [status(thm)], ['0', '23', '34'])).
% 59.92/60.11  
% 59.92/60.11  % SZS output end Refutation
% 59.92/60.11  
% 59.95/60.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
