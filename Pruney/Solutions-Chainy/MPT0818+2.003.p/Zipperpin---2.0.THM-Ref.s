%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ao8THosdXt

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 405 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) @ X8 ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('10',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['2','14'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X17 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ao8THosdXt
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:13:46 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 76 iterations in 0.054s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(t14_relset_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.19/0.51       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.19/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.19/0.51          ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.19/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t14_relset_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t193_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X8 : $i, X9 : $i]:
% 0.19/0.51         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) @ X8)),
% 0.19/0.51      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t3_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X3 : $i, X4 : $i]:
% 0.19/0.51         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('5', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf(t25_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( v1_relat_1 @ B ) =>
% 0.19/0.51           ( ( r1_tarski @ A @ B ) =>
% 0.19/0.51             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.51               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X10)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.19/0.51          | ~ (r1_tarski @ X11 @ X10)
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.51        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.19/0.51           (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.19/0.51        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( v1_relat_1 @ C ) ))).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X12)
% 0.19/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('10', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf(fc6_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.19/0.51        (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.19/0.51  thf(t1_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.51       ( r1_tarski @ A @ C ) ))).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.51          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.51          | (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 0.19/0.51          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '14'])).
% 0.19/0.51  thf(t11_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ C ) =>
% 0.19/0.51       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.19/0.51           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.19/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.51         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.19/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ X17)
% 0.19/0.51          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.19/0.51          | ~ (v1_relat_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ sk_D)
% 0.19/0.51          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.19/0.51          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.19/0.51          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '19'])).
% 0.19/0.51  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
