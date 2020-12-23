%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6u3YBEuOI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 171 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  303 (1626 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('18',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B_1 )
      | ~ ( r2_hidden @ X19 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('27',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6u3YBEuOI
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 45 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.48  thf(t6_relset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.48       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.48            ( ![E:$i,F:$i]:
% 0.20/0.48              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.48                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.48          ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.48               ( ![E:$i,F:$i]:
% 0.20/0.48                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.20/0.48                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.20/0.48  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t4_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.20/0.48          | (m1_subset_1 @ X15 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(t2_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ X13 @ X14)
% 0.20/0.48          | (v1_xboole_0 @ X14)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))
% 0.20/0.48        | (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_subset_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.48          | (v1_xboole_0 @ X11)
% 0.20/0.48          | ~ (v1_xboole_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))
% 0.20/0.48        | (v1_xboole_0 @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('12', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '12'])).
% 0.20/0.48  thf('14', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '13'])).
% 0.20/0.48  thf(l139_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.48          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3))
% 0.20/0.48          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.48  thf('16', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '13'])).
% 0.20/0.48  thf('18', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf(l54_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((r2_hidden @ X6 @ X7)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_A) @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((r2_hidden @ (sk_D @ sk_A) @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X18 @ sk_B_1)
% 0.20/0.48          | ~ (r2_hidden @ X19 @ sk_C)
% 0.20/0.48          | ((sk_A) != (k4_tarski @ X18 @ X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) != (k4_tarski @ (sk_D @ sk_A) @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '23'])).
% 0.20/0.48  thf('25', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '13'])).
% 0.20/0.48  thf('27', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((r2_hidden @ X8 @ X9)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf('31', plain, ($false), inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
