%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E4F20oxmtm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  397 ( 683 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('34',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('36',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E4F20oxmtm
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 437 iterations in 0.179s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.62  thf(t35_subset_1, conjecture,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62       ( ![C:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.36/0.62             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i,B:$i]:
% 0.36/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62          ( ![C:$i]:
% 0.36/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.36/0.62                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.36/0.62  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(d2_subset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (![X21 : $i, X22 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X21 @ X22)
% 0.36/0.62          | (r2_hidden @ X21 @ X22)
% 0.36/0.62          | (v1_xboole_0 @ X22))),
% 0.36/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.62        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.62  thf(fc1_subset_1, axiom,
% 0.36/0.62    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.62  thf('4', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.36/0.62      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.62  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['3', '4'])).
% 0.36/0.62  thf(d1_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.36/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X19 @ X18)
% 0.36/0.62          | (r1_tarski @ X19 @ X17)
% 0.36/0.62          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.36/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (![X17 : $i, X19 : $i]:
% 0.36/0.62         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.62  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.36/0.62      inference('sup-', [status(thm)], ['5', '7'])).
% 0.36/0.62  thf(d10_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.62  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.62  thf('11', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(d5_subset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X24 : $i, X25 : $i]:
% 0.36/0.62         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.36/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.36/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.62  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.62  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.62  thf(t85_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X10 @ X11)
% 0.36/0.62          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf(t86_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.36/0.62       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X13 @ X14)
% 0.36/0.62          | ~ (r1_xboole_0 @ X13 @ X15)
% 0.36/0.62          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         ((r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.36/0.62          | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['14', '19'])).
% 0.36/0.62  thf(t36_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.36/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X0 : $i, X2 : $i]:
% 0.36/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.62          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['20', '23'])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['13', '24'])).
% 0.36/0.62  thf('26', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X10 @ X11)
% 0.36/0.62          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (r1_xboole_0 @ sk_B @ 
% 0.36/0.62          (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.62  thf('29', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.36/0.62      inference('sup+', [status(thm)], ['25', '28'])).
% 0.36/0.62  thf('30', plain,
% 0.36/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X13 @ X14)
% 0.36/0.62          | ~ (r1_xboole_0 @ X13 @ X15)
% 0.36/0.62          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.36/0.62          | ~ (r1_tarski @ sk_B @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['10', '31'])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.62          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.62  thf('34', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('36', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.36/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (r1_tarski @ X13 @ X14)
% 0.36/0.62          | ~ (r1_xboole_0 @ X13 @ X15)
% 0.36/0.62          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.36/0.62          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.62  thf('39', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.62      inference('sup-', [status(thm)], ['8', '38'])).
% 0.36/0.62  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X24 : $i, X25 : $i]:
% 0.36/0.62         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.36/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.36/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.62  thf('43', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '42'])).
% 0.36/0.62  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
