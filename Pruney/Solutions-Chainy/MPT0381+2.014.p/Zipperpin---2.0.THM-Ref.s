%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xgmwjPS9DR

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  264 ( 500 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_A @ sk_B_2 ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( m1_subset_1 @ ( k1_tarski @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','10'])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['26','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xgmwjPS9DR
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 53 iterations in 0.033s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(t7_xboole_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X10 : $i]:
% 0.19/0.47         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X10) @ X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.47  thf('1', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.47  thf(t100_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X11 @ X12)
% 0.19/0.47           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(d5_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X7 @ X6)
% 0.19/0.47          | (r2_hidden @ X7 @ X4)
% 0.19/0.47          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.19/0.47         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X7 @ X6)
% 0.19/0.47          | ~ (r2_hidden @ X7 @ X5)
% 0.19/0.47          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X7 @ X5)
% 0.19/0.47          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.19/0.47          | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '10'])).
% 0.19/0.47  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '11'])).
% 0.19/0.47  thf(t63_subset_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.47       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( r2_hidden @ A @ B ) =>
% 0.19/0.47          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.19/0.47  thf('13', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d1_xboole_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf('15', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d2_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X23 : $i, X24 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X23 @ X24)
% 0.19/0.47          | (m1_subset_1 @ X23 @ X24)
% 0.19/0.47          | (v1_xboole_0 @ X24))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X23 : $i, X24 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.19/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain, ((m1_subset_1 @ sk_A @ sk_B_2)),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '19'])).
% 0.19/0.47  thf(t55_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ A ) =>
% 0.19/0.47       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.47         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X26 : $i, X27 : $i]:
% 0.19/0.47         (((X26) = (k1_xboole_0))
% 0.19/0.47          | ~ (m1_subset_1 @ X27 @ X26)
% 0.19/0.47          | (m1_subset_1 @ (k1_tarski @ X27) @ (k1_zfmisc_1 @ X26)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.19/0.47        | ((sk_B_2) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.19/0.47      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('demod', [status(thm)], ['15', '24'])).
% 0.19/0.47  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '25'])).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('clc', [status(thm)], ['6', '10'])).
% 0.19/0.47  thf('29', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.47  thf('30', plain, ($false), inference('demod', [status(thm)], ['26', '29'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
