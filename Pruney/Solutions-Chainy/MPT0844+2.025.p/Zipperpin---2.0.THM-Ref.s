%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bsyjl5PR6l

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  369 ( 715 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t55_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_xboole_0 @ B @ C )
       => ( ( k5_relset_1 @ C @ A @ D @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( ( r1_xboole_0 @ B @ C )
         => ( ( k5_relset_1 @ C @ A @ D @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_relset_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X6 @ X4 ) @ X5 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k5_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) )
      | ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( v1_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k5_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('30',plain,(
    ( k7_relat_1 @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bsyjl5PR6l
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:37:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 45 iterations in 0.037s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.51  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(t55_relset_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.51       ( ( r1_xboole_0 @ B @ C ) =>
% 0.23/0.51         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.51          ( ( r1_xboole_0 @ B @ C ) =>
% 0.23/0.51            ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t55_relset_1])).
% 0.23/0.51  thf('0', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t207_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( r1_xboole_0 @ A @ B ) =>
% 0.23/0.51         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.51         (~ (r1_xboole_0 @ X4 @ X5)
% 0.23/0.51          | ~ (v1_relat_1 @ X6)
% 0.23/0.51          | ((k7_relat_1 @ (k7_relat_1 @ X6 @ X4) @ X5) = (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_C) = (k1_xboole_0))
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(dt_k5_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( m1_subset_1 @
% 0.23/0.51         ( k5_relset_1 @ A @ B @ C @ D ) @ 
% 0.23/0.51         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.23/0.51          | (m1_subset_1 @ (k5_relset_1 @ X13 @ X14 @ X12 @ X15) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k5_relset_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(cc2_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.51         ((v4_relat_1 @ X9 @ X10)
% 0.23/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (v4_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ sk_C)),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf(t209_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.23/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X7 : $i, X8 : $i]:
% 0.23/0.51         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.23/0.51          | ~ (v4_relat_1 @ X7 @ X8)
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0))
% 0.23/0.51          | ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0)
% 0.23/0.51              = (k7_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ sk_C)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(cc2_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.51          | (v1_relat_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 0.23/0.51          | (v1_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf(fc6_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i]: (v1_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0)
% 0.23/0.51           = (k7_relat_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ sk_C))),
% 0.23/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k5_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.23/0.51          | ((k5_relset_1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k7_relat_1 @ sk_D @ X0)
% 0.23/0.51           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_C))),
% 0.23/0.51      inference('demod', [status(thm)], ['15', '18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      ((((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup+', [status(thm)], ['2', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.51          | (v1_relat_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.51  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['21', '26'])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      (((k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('30', plain, (((k7_relat_1 @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.51  thf('31', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
