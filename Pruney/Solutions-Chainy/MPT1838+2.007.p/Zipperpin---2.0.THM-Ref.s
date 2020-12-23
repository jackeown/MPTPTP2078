%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TceQ6Da4mP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:15 EST 2020

% Result     : Theorem 31.68s
% Output     : Refutation 31.68s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  316 ( 575 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( X32
        = ( k6_domain_1 @ X32 @ ( sk_B_1 @ X32 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( m1_subset_1 @ ( sk_B_1 @ X32 ) @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TceQ6Da4mP
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 31.68/31.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.68/31.87  % Solved by: fo/fo7.sh
% 31.68/31.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.68/31.87  % done 16778 iterations in 31.408s
% 31.68/31.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.68/31.87  % SZS output start Refutation
% 31.68/31.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.68/31.87  thf(sk_B_2_type, type, sk_B_2: $i).
% 31.68/31.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.68/31.87  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 31.68/31.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.68/31.87  thf(sk_B_type, type, sk_B: $i > $i).
% 31.68/31.87  thf(sk_A_type, type, sk_A: $i).
% 31.68/31.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 31.68/31.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 31.68/31.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 31.68/31.87  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 31.68/31.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.68/31.87  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 31.68/31.87  thf(t1_tex_2, conjecture,
% 31.68/31.87    (![A:$i]:
% 31.68/31.87     ( ( ~( v1_xboole_0 @ A ) ) =>
% 31.68/31.87       ( ![B:$i]:
% 31.68/31.87         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 31.68/31.87           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 31.68/31.87  thf(zf_stmt_0, negated_conjecture,
% 31.68/31.87    (~( ![A:$i]:
% 31.68/31.87        ( ( ~( v1_xboole_0 @ A ) ) =>
% 31.68/31.87          ( ![B:$i]:
% 31.68/31.87            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 31.68/31.87              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 31.68/31.87    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 31.68/31.87  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf(d1_tex_2, axiom,
% 31.68/31.87    (![A:$i]:
% 31.68/31.87     ( ( ~( v1_xboole_0 @ A ) ) =>
% 31.68/31.87       ( ( v1_zfmisc_1 @ A ) <=>
% 31.68/31.87         ( ?[B:$i]:
% 31.68/31.87           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 31.68/31.87  thf('1', plain,
% 31.68/31.87      (![X32 : $i]:
% 31.68/31.87         (~ (v1_zfmisc_1 @ X32)
% 31.68/31.87          | ((X32) = (k6_domain_1 @ X32 @ (sk_B_1 @ X32)))
% 31.68/31.87          | (v1_xboole_0 @ X32))),
% 31.68/31.87      inference('cnf', [status(esa)], [d1_tex_2])).
% 31.68/31.87  thf('2', plain,
% 31.68/31.87      (![X32 : $i]:
% 31.68/31.87         (~ (v1_zfmisc_1 @ X32)
% 31.68/31.87          | (m1_subset_1 @ (sk_B_1 @ X32) @ X32)
% 31.68/31.87          | (v1_xboole_0 @ X32))),
% 31.68/31.87      inference('cnf', [status(esa)], [d1_tex_2])).
% 31.68/31.87  thf(redefinition_k6_domain_1, axiom,
% 31.68/31.87    (![A:$i,B:$i]:
% 31.68/31.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 31.68/31.87       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 31.68/31.87  thf('3', plain,
% 31.68/31.87      (![X30 : $i, X31 : $i]:
% 31.68/31.87         ((v1_xboole_0 @ X30)
% 31.68/31.87          | ~ (m1_subset_1 @ X31 @ X30)
% 31.68/31.87          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 31.68/31.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 31.68/31.87  thf('4', plain,
% 31.68/31.87      (![X0 : $i]:
% 31.68/31.87         ((v1_xboole_0 @ X0)
% 31.68/31.87          | ~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 31.68/31.87          | (v1_xboole_0 @ X0))),
% 31.68/31.87      inference('sup-', [status(thm)], ['2', '3'])).
% 31.68/31.87  thf('5', plain,
% 31.68/31.87      (![X0 : $i]:
% 31.68/31.87         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 31.68/31.87          | ~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | (v1_xboole_0 @ X0))),
% 31.68/31.87      inference('simplify', [status(thm)], ['4'])).
% 31.68/31.87  thf('6', plain,
% 31.68/31.87      (![X0 : $i]:
% 31.68/31.87         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 31.68/31.87          | (v1_xboole_0 @ X0)
% 31.68/31.87          | ~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | (v1_xboole_0 @ X0)
% 31.68/31.87          | ~ (v1_zfmisc_1 @ X0))),
% 31.68/31.87      inference('sup+', [status(thm)], ['1', '5'])).
% 31.68/31.87  thf('7', plain,
% 31.68/31.87      (![X0 : $i]:
% 31.68/31.87         (~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | (v1_xboole_0 @ X0)
% 31.68/31.87          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 31.68/31.87      inference('simplify', [status(thm)], ['6'])).
% 31.68/31.87  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('9', plain,
% 31.68/31.87      (![X0 : $i]:
% 31.68/31.87         (~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | (v1_xboole_0 @ X0)
% 31.68/31.87          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 31.68/31.87      inference('simplify', [status(thm)], ['6'])).
% 31.68/31.87  thf(l3_zfmisc_1, axiom,
% 31.68/31.87    (![A:$i,B:$i]:
% 31.68/31.87     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 31.68/31.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 31.68/31.87  thf('10', plain,
% 31.68/31.87      (![X25 : $i, X26 : $i]:
% 31.68/31.87         (((X26) = (k1_tarski @ X25))
% 31.68/31.87          | ((X26) = (k1_xboole_0))
% 31.68/31.87          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 31.68/31.87      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 31.68/31.87  thf('11', plain,
% 31.68/31.87      (![X0 : $i, X1 : $i]:
% 31.68/31.87         (~ (r1_tarski @ X1 @ X0)
% 31.68/31.87          | (v1_xboole_0 @ X0)
% 31.68/31.87          | ~ (v1_zfmisc_1 @ X0)
% 31.68/31.87          | ((X1) = (k1_xboole_0))
% 31.68/31.87          | ((X1) = (k1_tarski @ (sk_B_1 @ X0))))),
% 31.68/31.87      inference('sup-', [status(thm)], ['9', '10'])).
% 31.68/31.87  thf('12', plain,
% 31.68/31.87      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 31.68/31.87        | ((sk_A) = (k1_xboole_0))
% 31.68/31.87        | ~ (v1_zfmisc_1 @ sk_B_2)
% 31.68/31.87        | (v1_xboole_0 @ sk_B_2))),
% 31.68/31.87      inference('sup-', [status(thm)], ['8', '11'])).
% 31.68/31.87  thf('13', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('14', plain,
% 31.68/31.87      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 31.68/31.87        | ((sk_A) = (k1_xboole_0))
% 31.68/31.87        | (v1_xboole_0 @ sk_B_2))),
% 31.68/31.87      inference('demod', [status(thm)], ['12', '13'])).
% 31.68/31.87  thf('15', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('16', plain,
% 31.68/31.87      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 31.68/31.87      inference('clc', [status(thm)], ['14', '15'])).
% 31.68/31.87  thf('17', plain,
% 31.68/31.87      ((((sk_A) = (sk_B_2))
% 31.68/31.87        | (v1_xboole_0 @ sk_B_2)
% 31.68/31.87        | ~ (v1_zfmisc_1 @ sk_B_2)
% 31.68/31.87        | ((sk_A) = (k1_xboole_0)))),
% 31.68/31.87      inference('sup+', [status(thm)], ['7', '16'])).
% 31.68/31.87  thf('18', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('19', plain,
% 31.68/31.87      ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 31.68/31.87      inference('demod', [status(thm)], ['17', '18'])).
% 31.68/31.87  thf('20', plain, (((sk_A) != (sk_B_2))),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('21', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 31.68/31.87      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 31.68/31.87  thf('22', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 31.68/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.68/31.87  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 31.68/31.87      inference('clc', [status(thm)], ['21', '22'])).
% 31.68/31.87  thf(commutativity_k2_xboole_0, axiom,
% 31.68/31.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 31.68/31.87  thf('24', plain,
% 31.68/31.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.68/31.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.68/31.87  thf(t1_boole, axiom,
% 31.68/31.87    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 31.68/31.87  thf('25', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 31.68/31.87      inference('cnf', [status(esa)], [t1_boole])).
% 31.68/31.87  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 31.68/31.87      inference('sup+', [status(thm)], ['24', '25'])).
% 31.68/31.87  thf(t7_xboole_1, axiom,
% 31.68/31.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 31.68/31.87  thf('27', plain,
% 31.68/31.87      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 31.68/31.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 31.68/31.87  thf('28', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 31.68/31.87      inference('sup+', [status(thm)], ['26', '27'])).
% 31.68/31.87  thf(d1_xboole_0, axiom,
% 31.68/31.87    (![A:$i]:
% 31.68/31.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 31.68/31.87  thf('29', plain,
% 31.68/31.87      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 31.68/31.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 31.68/31.87  thf(t7_ordinal1, axiom,
% 31.68/31.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 31.68/31.87  thf('30', plain,
% 31.68/31.87      (![X28 : $i, X29 : $i]:
% 31.68/31.87         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 31.68/31.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 31.68/31.87  thf('31', plain,
% 31.68/31.87      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 31.68/31.87      inference('sup-', [status(thm)], ['29', '30'])).
% 31.68/31.87  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 31.68/31.87      inference('sup-', [status(thm)], ['28', '31'])).
% 31.68/31.87  thf('33', plain, ($false),
% 31.68/31.87      inference('demod', [status(thm)], ['0', '23', '32'])).
% 31.68/31.87  
% 31.68/31.87  % SZS output end Refutation
% 31.68/31.87  
% 31.68/31.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
