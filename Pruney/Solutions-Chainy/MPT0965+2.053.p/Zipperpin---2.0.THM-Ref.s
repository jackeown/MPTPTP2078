%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDFwW6WmWF

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  266 ( 542 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X10 ) @ ( k2_relset_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDFwW6WmWF
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 39 iterations in 0.025s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.45  thf(t7_funct_2, conjecture,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.45         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.45           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.45            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45          ( ( r2_hidden @ C @ A ) =>
% 0.21/0.45            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.45              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.21/0.45  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t6_funct_2, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.45         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.45           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.45          | ((X12) = (k1_xboole_0))
% 0.21/0.45          | ~ (v1_funct_1 @ X13)
% 0.21/0.45          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.21/0.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.21/0.45          | (r2_hidden @ (k1_funct_1 @ X13 @ X10) @ 
% 0.21/0.45             (k2_relset_1 @ X11 @ X12 @ X13)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.45           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.45          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.21/0.45          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.45          | ((sk_B) = (k1_xboole_0))
% 0.21/0.45          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.45  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.45           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.45          | ((sk_B) = (k1_xboole_0))
% 0.21/0.45          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.45  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.45           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.45          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ 
% 0.21/0.45        (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '9'])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(dt_k2_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.45         ((m1_subset_1 @ (k2_relset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.21/0.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i]:
% 0.21/0.45         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('15', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.45  thf(d3_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.45          | (r2_hidden @ X0 @ X2)
% 0.21/0.45          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ X0 @ sk_B)
% 0.21/0.45          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['10', '17'])).
% 0.21/0.45  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
