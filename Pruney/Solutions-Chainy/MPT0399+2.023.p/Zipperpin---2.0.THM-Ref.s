%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dVAgX4mK0Z

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 117 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  207 ( 677 expanded)
%              Number of equality atoms :   11 (  44 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_setfam_1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,
    ( ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','18'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference('sup-',[status(thm)],['20','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dVAgX4mK0Z
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 24 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t7_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(t21_setfam_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.47  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.47              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_D @ X3 @ X4) @ X4)
% 0.21/0.47          | ~ (r2_hidden @ X3 @ X5)
% 0.21/0.47          | ~ (r1_setfam_1 @ X5 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))
% 0.21/0.47        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.47  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(l49_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (r2_hidden @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((r1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ 
% 0.21/0.47        (k3_tarski @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf('11', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((r1_tarski @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X10 : $i, X12 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ 
% 0.21/0.47        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(t5_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.47          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.47          | ~ (v1_xboole_0 @ X15)
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain, (((sk_D @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '18'])).
% 0.21/0.47  thf('20', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('22', plain, (((sk_D @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '18'])).
% 0.21/0.47  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ($false), inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
