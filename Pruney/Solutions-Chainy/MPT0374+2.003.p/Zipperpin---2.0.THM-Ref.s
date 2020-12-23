%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cv5fmcqQiU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:23 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 ( 518 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t56_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ( ( A != k1_xboole_0 )
           => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( ( A != k1_xboole_0 )
             => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ( k1_subset_1 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_subset_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X35: $i] :
      ( ( k1_subset_1 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['8','9'])).

thf('16',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(clc,[status(thm)],['14','15'])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X28 @ X30 ) @ X31 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C_2 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','18'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ ( k2_tarski @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( m1_subset_1 @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X32: $i,X33: $i] :
      ( ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(clc,[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cv5fmcqQiU
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 612 iterations in 0.419s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.88  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.70/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.88  thf(t56_subset_1, conjecture,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ B @ A ) =>
% 0.70/0.88       ( ![C:$i]:
% 0.70/0.88         ( ( m1_subset_1 @ C @ A ) =>
% 0.70/0.88           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.70/0.88             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i,B:$i]:
% 0.70/0.88        ( ( m1_subset_1 @ B @ A ) =>
% 0.70/0.88          ( ![C:$i]:
% 0.70/0.88            ( ( m1_subset_1 @ C @ A ) =>
% 0.70/0.88              ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.70/0.88                ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t56_subset_1])).
% 0.70/0.88  thf('0', plain,
% 0.70/0.88      (~ (m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(d2_subset_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( ( v1_xboole_0 @ A ) =>
% 0.70/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.70/0.88       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.70/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.88  thf('2', plain,
% 0.70/0.88      (![X32 : $i, X33 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X32 @ X33)
% 0.70/0.88          | (r2_hidden @ X32 @ X33)
% 0.70/0.88          | (v1_xboole_0 @ X33))),
% 0.70/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.70/0.88  thf('3', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.88  thf(l13_xboole_0, axiom,
% 0.70/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.88  thf('4', plain,
% 0.70/0.88      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 0.70/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.88  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('5', plain, (![X35 : $i]: ((k1_subset_1 @ X35) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.88  thf('6', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (((k1_subset_1 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('8', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((k1_subset_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.88  thf('9', plain, (![X35 : $i]: ((k1_subset_1 @ X35) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.88  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.70/0.88      inference('simplify_reflect+', [status(thm)], ['8', '9'])).
% 0.70/0.88  thf('11', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.70/0.88      inference('clc', [status(thm)], ['3', '10'])).
% 0.70/0.88  thf('12', plain, ((m1_subset_1 @ sk_C_2 @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X32 : $i, X33 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X32 @ X33)
% 0.70/0.88          | (r2_hidden @ X32 @ X33)
% 0.70/0.88          | (v1_xboole_0 @ X33))),
% 0.70/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.70/0.88  thf('14', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_2 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.88  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.70/0.88      inference('simplify_reflect+', [status(thm)], ['8', '9'])).
% 0.70/0.88  thf('16', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.70/0.88      inference('clc', [status(thm)], ['14', '15'])).
% 0.70/0.88  thf(t73_zfmisc_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.70/0.88       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.70/0.88         (((k4_xboole_0 @ (k2_tarski @ X28 @ X30) @ X31) = (k1_xboole_0))
% 0.70/0.88          | ~ (r2_hidden @ X30 @ X31)
% 0.70/0.88          | ~ (r2_hidden @ X28 @ X31))),
% 0.70/0.88      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.70/0.88  thf('18', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X0 @ sk_A)
% 0.70/0.88          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_C_2) @ sk_A) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C_2) @ sk_A) = (k1_xboole_0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '18'])).
% 0.70/0.88  thf(l32_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.88  thf('20', plain,
% 0.70/0.88      (![X7 : $i, X8 : $i]:
% 0.70/0.88         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.70/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.88        | (r1_tarski @ (k2_tarski @ sk_B @ sk_C_2) @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.70/0.88  thf('22', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_C_2) @ sk_A)),
% 0.70/0.88      inference('simplify', [status(thm)], ['21'])).
% 0.70/0.88  thf(d1_zfmisc_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.70/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.70/0.88  thf('23', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X18 @ X19)
% 0.70/0.88          | (r2_hidden @ X18 @ X20)
% 0.70/0.88          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.70/0.88      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((r2_hidden @ X18 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 0.70/0.88      inference('simplify', [status(thm)], ['23'])).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      ((r2_hidden @ (k2_tarski @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['22', '24'])).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (![X32 : $i, X33 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X32 @ X33)
% 0.70/0.88          | (m1_subset_1 @ X32 @ X33)
% 0.70/0.88          | (v1_xboole_0 @ X33))),
% 0.70/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.70/0.88  thf('27', plain,
% 0.70/0.88      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 0.70/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.88  thf(t4_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t4_boole])).
% 0.70/0.88  thf(d5_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.70/0.88       ( ![D:$i]:
% 0.70/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.88           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X4 @ X3)
% 0.70/0.88          | ~ (r2_hidden @ X4 @ X2)
% 0.70/0.88          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X4 @ X2)
% 0.70/0.88          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['29'])).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['28', '30'])).
% 0.70/0.88  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.70/0.88      inference('condensation', [status(thm)], ['31'])).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['27', '32'])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      (![X32 : $i, X33 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X32 @ X33) | ~ (r2_hidden @ X32 @ X33))),
% 0.70/0.88      inference('clc', [status(thm)], ['26', '33'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      ((m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['25', '34'])).
% 0.70/0.88  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.70/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
