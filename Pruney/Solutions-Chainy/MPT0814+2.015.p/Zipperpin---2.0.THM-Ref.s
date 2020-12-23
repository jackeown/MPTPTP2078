%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LZun6Jexyh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 122 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (1116 expanded)
%              Number of equality atoms :   15 (  59 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X8 ) @ ( sk_E @ X8 ) )
        = X8 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('11',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('13',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_B )
      | ~ ( r2_hidden @ X20 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('22',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['20','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LZun6Jexyh
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 119 iterations in 0.056s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(t6_relset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.49       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.50            ( ![E:$i,F:$i]:
% 0.20/0.50              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.50                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.50          ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.50               ( ![E:$i,F:$i]:
% 0.20/0.50                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.20/0.50                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.20/0.50  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('3', plain, ((r1_tarski @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(t28_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((k3_xboole_0 @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C)) = (sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(d4_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.50          | (r2_hidden @ X4 @ X2)
% 0.20/0.50          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_D_2)
% 0.20/0.50          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.50  thf('9', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '8'])).
% 0.20/0.50  thf(l139_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.50          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (((k4_tarski @ (sk_D_1 @ X8) @ (sk_E @ X8)) = (X8))
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.50  thf('11', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '8'])).
% 0.20/0.50  thf('13', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(l54_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((r2_hidden @ X11 @ X12)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X19 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ X20 @ sk_C)
% 0.20/0.50          | ((sk_A) != (k4_tarski @ X19 @ X20)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) != (k4_tarski @ (sk_D_1 @ sk_A) @ X0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.50  thf('20', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.50  thf('21', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '8'])).
% 0.20/0.50  thf('22', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((r2_hidden @ X13 @ X14)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.50  thf('26', plain, ($false), inference('demod', [status(thm)], ['20', '25'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
