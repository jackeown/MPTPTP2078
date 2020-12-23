%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8aIx8zkElm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 101 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 ( 926 expanded)
%              Number of equality atoms :   10 (  34 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X4 ) @ ( sk_E @ X4 ) )
        = X4 )
      | ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('8',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('10',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B )
      | ~ ( r2_hidden @ X16 @ sk_C_1 )
      | ( sk_A
       != ( k4_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('19',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['17','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8aIx8zkElm
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 59 iterations in 0.028s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(t6_relset_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.50       ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.50            ( ![E:$i,F:$i]:
% 0.21/0.50              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.50                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.50          ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.50               ( ![E:$i,F:$i]:
% 0.21/0.50                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.21/0.50                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('3', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.50  thf(l139_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.50          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (((k4_tarski @ (sk_D @ X4) @ (sk_E @ X4)) = (X4))
% 0.21/0.50          | ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.50  thf('8', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.50  thf('10', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(l54_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((r2_hidden @ X7 @ X8)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ (sk_D @ sk_A) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r2_hidden @ (sk_D @ sk_A) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X15 @ sk_B)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ sk_C_1)
% 0.21/0.50          | ((sk_A) != (k4_tarski @ X15 @ X16)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_A) != (k4_tarski @ (sk_D @ sk_A) @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '15'])).
% 0.21/0.50  thf('17', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf('18', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.50  thf('19', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((r2_hidden @ X9 @ X10)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.50  thf('23', plain, ($false), inference('demod', [status(thm)], ['17', '22'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
