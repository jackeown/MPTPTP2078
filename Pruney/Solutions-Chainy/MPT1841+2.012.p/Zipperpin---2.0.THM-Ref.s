%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UdZOaD4lJN

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  418 ( 645 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( ( k6_domain_1 @ X28 @ X29 )
        = ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_zfmisc_1 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X5 @ X6 @ X7 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X14 @ X19 )
      | ( X19
       != ( k2_enumset1 @ X18 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X14 @ ( k2_enumset1 @ X18 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X12 @ X8 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UdZOaD4lJN
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 38 iterations in 0.022s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.45  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(t6_tex_2, conjecture,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( m1_subset_1 @ B @ A ) =>
% 0.19/0.45           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.19/0.45                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]:
% 0.19/0.45        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.45          ( ![B:$i]:
% 0.19/0.45            ( ( m1_subset_1 @ B @ A ) =>
% 0.19/0.45              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.19/0.45                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.19/0.45  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(dt_k6_domain_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.45       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X26 : $i, X27 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ X26)
% 0.19/0.45          | ~ (m1_subset_1 @ X27 @ X26)
% 0.19/0.45          | (m1_subset_1 @ (k6_domain_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26)))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.45        | (v1_xboole_0 @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.45       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X28 : $i, X29 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ X28)
% 0.19/0.45          | ~ (m1_subset_1 @ X29 @ X28)
% 0.19/0.45          | ((k6_domain_1 @ X28 @ X29) = (k1_tarski @ X29)))),
% 0.19/0.45      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.45        | (v1_xboole_0 @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.45  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.19/0.45      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.45        | (v1_xboole_0 @ sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['2', '7'])).
% 0.19/0.45  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.45      inference('clc', [status(thm)], ['8', '9'])).
% 0.19/0.45  thf(cc2_tex_2, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.45           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X30 : $i, X31 : $i]:
% 0.19/0.45         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.19/0.45          | ~ (v1_subset_1 @ X30 @ X31)
% 0.19/0.45          | (v1_xboole_0 @ X30)
% 0.19/0.45          | ~ (v1_zfmisc_1 @ X31)
% 0.19/0.45          | (v1_xboole_0 @ X31))),
% 0.19/0.45      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (((v1_xboole_0 @ sk_A)
% 0.19/0.45        | ~ (v1_zfmisc_1 @ sk_A)
% 0.19/0.45        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.19/0.45        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.45  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.19/0.45      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.19/0.45      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.19/0.45      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.19/0.45  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.19/0.45      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.45  thf(l13_xboole_0, axiom,
% 0.19/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.45  thf('20', plain,
% 0.19/0.45      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.45      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.45  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.45  thf(t69_enumset1, axiom,
% 0.19/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.45  thf('22', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.45  thf(t70_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i]:
% 0.19/0.45         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.45  thf(t71_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.45         ((k2_enumset1 @ X5 @ X5 @ X6 @ X7) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.45  thf(d2_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.45     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.45       ( ![F:$i]:
% 0.19/0.45         ( ( r2_hidden @ F @ E ) <=>
% 0.19/0.45           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.19/0.45                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.45  thf(zf_stmt_2, axiom,
% 0.19/0.45    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.45     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.19/0.45       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.19/0.45         ( ( F ) != ( D ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_3, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.45     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.45       ( ![F:$i]:
% 0.19/0.45         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.19/0.45  thf('25', plain,
% 0.19/0.45      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.45         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.19/0.45          | (r2_hidden @ X14 @ X19)
% 0.19/0.45          | ((X19) != (k2_enumset1 @ X18 @ X17 @ X16 @ X15)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.45  thf('26', plain,
% 0.19/0.45      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.45         ((r2_hidden @ X14 @ (k2_enumset1 @ X18 @ X17 @ X16 @ X15))
% 0.19/0.45          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.19/0.45      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.45  thf(t7_ordinal1, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.45  thf('27', plain,
% 0.19/0.45      (![X24 : $i, X25 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.19/0.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.45         ((zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3)
% 0.19/0.45          | ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.19/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.45  thf('29', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.19/0.45          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.19/0.45      inference('sup-', [status(thm)], ['24', '28'])).
% 0.19/0.45  thf('30', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.19/0.45          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['23', '29'])).
% 0.19/0.45  thf('31', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.19/0.45          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['22', '30'])).
% 0.19/0.45  thf('32', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.19/0.45          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['21', '31'])).
% 0.19/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.45  thf('33', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf('34', plain,
% 0.19/0.45      (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B)),
% 0.19/0.45      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.45  thf('35', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.45         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.45         ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X12 @ X8)),
% 0.19/0.45      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.45  thf('37', plain, ($false), inference('sup-', [status(thm)], ['34', '36'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
