%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AyYqq2PBHL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:41 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   62 (  83 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  430 ( 611 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X48 @ X47 ) @ X47 )
      | ( r1_tarski @ X48 @ ( k1_setfam_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r1_tarski @ X49 @ X51 )
      | ( r1_tarski @ ( k1_setfam_1 @ X50 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( sk_C_2 @ X48 @ X47 ) )
      | ( r1_tarski @ X48 @ ( k1_setfam_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('21',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('34',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 != X38 )
      | ~ ( r2_hidden @ X36 @ ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('35',plain,(
    ! [X37: $i,X38: $i] :
      ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AyYqq2PBHL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 422 iterations in 0.234s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.48/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(t6_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.48/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (![X47 : $i, X48 : $i]:
% 0.48/0.68         (((X47) = (k1_xboole_0))
% 0.48/0.68          | (r2_hidden @ (sk_C_2 @ X48 @ X47) @ X47)
% 0.48/0.68          | (r1_tarski @ X48 @ (k1_setfam_1 @ X47)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.48/0.68  thf(d1_tarski, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.48/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X28 @ X27)
% 0.48/0.68          | ((X28) = (X25))
% 0.48/0.68          | ((X27) != (k1_tarski @ X25)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X25 : $i, X28 : $i]:
% 0.48/0.68         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['1'])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.68          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('5', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.48/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.68         (((X26) != (X25))
% 0.48/0.68          | (r2_hidden @ X26 @ X27)
% 0.48/0.68          | ((X27) != (k1_tarski @ X25)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.68  thf('7', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.48/0.68      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.68  thf(t8_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.48/0.68       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X49 @ X50)
% 0.48/0.68          | ~ (r1_tarski @ X49 @ X51)
% 0.48/0.68          | (r1_tarski @ (k1_setfam_1 @ X50) @ X51))),
% 0.48/0.68      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.48/0.68          | ~ (r1_tarski @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['5', '9'])).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X10 : $i, X12 : $i]:
% 0.48/0.68         (((X10) = (X12))
% 0.48/0.68          | ~ (r1_tarski @ X12 @ X10)
% 0.48/0.68          | ~ (r1_tarski @ X10 @ X12))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.68          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['3', '12'])).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      (![X47 : $i, X48 : $i]:
% 0.48/0.68         (((X47) = (k1_xboole_0))
% 0.48/0.68          | ~ (r1_tarski @ X48 @ (sk_C_2 @ X48 @ X47))
% 0.48/0.68          | (r1_tarski @ X48 @ (k1_setfam_1 @ X47)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X0 @ X0)
% 0.48/0.68          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.68          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.68  thf('16', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.48/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.68          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.68          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('clc', [status(thm)], ['18', '19'])).
% 0.48/0.68  thf(t11_setfam_1, conjecture,
% 0.48/0.68    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.48/0.68  thf('21', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.68  thf('24', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.48/0.68      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.68  thf('25', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.48/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.68  thf(d5_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.48/0.68       ( ![D:$i]:
% 0.48/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.48/0.68         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.48/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.48/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.48/0.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.48/0.68      inference('eq_fact', [status(thm)], ['26'])).
% 0.48/0.68  thf(t4_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.48/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X41 : $i, X42 : $i]:
% 0.48/0.68         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('30', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.68  thf(d3_tarski, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.68          | (r2_hidden @ X0 @ X2)
% 0.48/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.48/0.68          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['27', '32'])).
% 0.48/0.68  thf(t64_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.48/0.68       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.68         (((X36) != (X38))
% 0.48/0.68          | ~ (r2_hidden @ X36 @ (k4_xboole_0 @ X37 @ (k1_tarski @ X38))))),
% 0.48/0.68      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X37 : $i, X38 : $i]:
% 0.48/0.68         ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X37 @ (k1_tarski @ X38)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '35'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X37 : $i, X38 : $i]:
% 0.48/0.68         ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X37 @ (k1_tarski @ X38)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.48/0.68  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.68  thf('39', plain, ($false), inference('sup-', [status(thm)], ['25', '38'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
