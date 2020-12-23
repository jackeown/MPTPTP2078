%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3iDIUmjofA

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 ( 433 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t14_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
         => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) @ X10 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['2','16'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X16 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3iDIUmjofA
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 78 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(t14_relset_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.50          ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.20/0.50            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t14_relset_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t193_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11)) @ X10)),
% 0.20/0.50      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('5', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(t25_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.50             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.50               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X12)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.20/0.50          | ~ (r1_tarski @ X13 @ X12)
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.50        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.20/0.50           (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.20/0.50        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.50          | (v1_relat_1 @ X6)
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.20/0.50        (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '12', '13'])).
% 0.20/0.50  thf(t1_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50       ( r1_tarski @ A @ C ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.50          | (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 0.20/0.50          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '16'])).
% 0.20/0.50  thf(t11_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.20/0.50           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X14) @ X16)
% 0.20/0.50          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.50          | ~ (v1_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ sk_D)
% 0.20/0.50          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.20/0.50          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.20/0.50          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '21'])).
% 0.20/0.50  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
