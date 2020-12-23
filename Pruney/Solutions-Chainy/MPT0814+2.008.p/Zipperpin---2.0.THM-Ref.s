%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v92qTCDzb8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 137 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 (1186 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X9 ) @ ( sk_E @ X9 ) )
        = X9 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('13',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('15',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_B )
      | ~ ( r2_hidden @ X21 @ sk_C_2 )
      | ( sk_A
       != ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('24',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['22','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v92qTCDzb8
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:59:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 133 iterations in 0.110s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(sk_E_type, type, sk_E: $i > $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(t6_relset_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.22/0.57       ( ~( ( r2_hidden @ A @ D ) & 
% 0.22/0.57            ( ![E:$i,F:$i]:
% 0.22/0.57              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.22/0.57                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.22/0.57          ( ~( ( r2_hidden @ A @ D ) & 
% 0.22/0.57               ( ![E:$i,F:$i]:
% 0.22/0.57                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.22/0.57                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.22/0.57  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t2_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i]:
% 0.22/0.57         ((r2_hidden @ X18 @ X19)
% 0.22/0.57          | (v1_xboole_0 @ X19)
% 0.22/0.57          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))
% 0.22/0.57        | (r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf(fc1_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('4', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      ((r2_hidden @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 0.22/0.57      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf(d1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X7 @ X6)
% 0.22/0.57          | (r1_tarski @ X7 @ X5)
% 0.22/0.57          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X5 : $i, X7 : $i]:
% 0.22/0.57         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('8', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.57  thf(d3_tarski, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.57          | (r2_hidden @ X0 @ X2)
% 0.22/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_2))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '10'])).
% 0.22/0.57  thf(l139_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.57          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.57         (((k4_tarski @ (sk_D @ X9) @ (sk_E @ X9)) = (X9))
% 0.22/0.57          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.22/0.57  thf('13', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf('14', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '10'])).
% 0.22/0.57  thf('15', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf(l54_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.57         ((r2_hidden @ X12 @ X13)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.57          | (r2_hidden @ (sk_D @ sk_A) @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain, ((r2_hidden @ (sk_D @ sk_A) @ sk_B)),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X20 : $i, X21 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X20 @ sk_B)
% 0.22/0.57          | ~ (r2_hidden @ X21 @ sk_C_2)
% 0.22/0.57          | ((sk_A) != (k4_tarski @ X20 @ X21)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((sk_A) != (k4_tarski @ (sk_D @ sk_A) @ X0))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['13', '20'])).
% 0.22/0.57  thf('22', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_2)),
% 0.22/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.57  thf('23', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '10'])).
% 0.22/0.57  thf('24', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.57         ((r2_hidden @ X14 @ X15)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.57          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.57  thf('27', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C_2)),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.57  thf('28', plain, ($false), inference('demod', [status(thm)], ['22', '27'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
