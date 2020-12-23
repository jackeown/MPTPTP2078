%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osGD0wRtgZ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 156 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  360 (1625 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
        = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','16'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','16'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['11','16'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_B )
      | ~ ( r2_hidden @ X17 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['20','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','35'])).

thf('37',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osGD0wRtgZ
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 40 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(t6_relset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.47       ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.47            ( ![E:$i,F:$i]:
% 0.21/0.47              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.47                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.47          ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.47               ( ![E:$i,F:$i]:
% 0.21/0.47                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.21/0.47                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.21/0.47  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t5_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.47          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.47          | ~ (v1_xboole_0 @ X15)
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.47          | (m1_subset_1 @ X10 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.47  thf(t2_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         ((r2_hidden @ X8 @ X9)
% 0.21/0.47          | (v1_xboole_0 @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(l139_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.47          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | ((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf(l54_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         ((r2_hidden @ X5 @ X6)
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.47          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.47  thf('21', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('22', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('24', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ X4)
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.47          | (r2_hidden @ (sk_D @ sk_A) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47        | (r2_hidden @ (sk_D @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_D @ sk_A) @ sk_B) | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, ((r2_hidden @ (sk_D @ sk_A) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X16 @ sk_B)
% 0.21/0.47          | ~ (r2_hidden @ X17 @ sk_C)
% 0.21/0.47          | ((sk_A) != (k4_tarski @ X16 @ X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) != (k4_tarski @ (sk_D @ sk_A) @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '32'])).
% 0.21/0.47  thf('34', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.21/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.47  thf('35', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.47      inference('clc', [status(thm)], ['20', '34'])).
% 0.21/0.47  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D_1)),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '35'])).
% 0.21/0.47  thf('37', plain, ($false), inference('sup-', [status(thm)], ['0', '36'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
