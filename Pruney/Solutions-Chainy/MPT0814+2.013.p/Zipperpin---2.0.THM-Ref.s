%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EClJu11dDL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 169 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  337 (1396 expanded)
%              Number of equality atoms :   17 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ sk_D_2 @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X8 ) @ ( sk_E @ X8 ) )
        = X8 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('17',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('19',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ~ ( r2_hidden @ X23 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('28',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['26','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EClJu11dDL
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 154 iterations in 0.110s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(t6_relset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.56       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.56            ( ![E:$i,F:$i]:
% 0.20/0.56              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.56                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.56          ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.56               ( ![E:$i,F:$i]:
% 0.20/0.56                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.20/0.56                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.20/0.56  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_2)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t2_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((r2_hidden @ X20 @ X21)
% 0.20/0.56          | (v1_xboole_0 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.20/0.56        | (r2_hidden @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf(fc1_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('4', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      ((r2_hidden @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.56      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf(l49_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((r1_tarski @ sk_D_2 @ 
% 0.20/0.56        (k3_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf(t99_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.56  thf('8', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.56  thf('9', plain, ((r1_tarski @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (((k3_xboole_0 @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C)) = (sk_D_2))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(d4_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | (r2_hidden @ X4 @ X2)
% 0.20/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_D_2)
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.56  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '14'])).
% 0.20/0.56  thf(l139_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.56          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (((k4_tarski @ (sk_D_1 @ X8) @ (sk_E @ X8)) = (X8))
% 0.20/0.56          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.56  thf('17', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('18', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '14'])).
% 0.20/0.56  thf('19', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf(l54_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         ((r2_hidden @ X13 @ X14)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.56          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X22 @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ X23 @ sk_C)
% 0.20/0.56          | ((sk_A) != (k4_tarski @ X22 @ X23)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_A) != (k4_tarski @ (sk_D_1 @ sk_A) @ X0))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '24'])).
% 0.20/0.56  thf('26', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.56  thf('27', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '14'])).
% 0.20/0.56  thf('28', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         ((r2_hidden @ X15 @ X16)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.56          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.56  thf('32', plain, ($false), inference('demod', [status(thm)], ['26', '31'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
