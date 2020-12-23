%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HsDPr3NyWw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 457 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k5_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['4','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HsDPr3NyWw
% 0.15/0.37  % Computer   : n005.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:59:48 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 240 iterations in 0.150s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.63  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.63  thf(t33_relset_1, conjecture,
% 0.39/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.39/0.63       ( m1_subset_1 @
% 0.39/0.63         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.39/0.63         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.39/0.63          ( m1_subset_1 @
% 0.39/0.63            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.39/0.63            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.39/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(redefinition_k5_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.63       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.39/0.63          | ((k5_relset_1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.63  thf('4', plain,
% 0.39/0.63      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.39/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.63  thf(t87_relat_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ B ) =>
% 0.39/0.63       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.39/0.63  thf('5', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.39/0.63          | ~ (v1_relat_1 @ X8))),
% 0.39/0.63      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(t3_subset, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      (![X3 : $i, X4 : $i]:
% 0.39/0.63         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.63  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.39/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.63  thf(t88_relat_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.39/0.63  thf('9', plain,
% 0.39/0.63      (![X10 : $i, X11 : $i]:
% 0.39/0.63         ((r1_tarski @ (k7_relat_1 @ X10 @ X11) @ X10) | ~ (v1_relat_1 @ X10))),
% 0.39/0.63      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.39/0.63  thf(t1_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.63       ( r1_tarski @ A @ C ) ))).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.63          | ~ (r1_tarski @ X1 @ X2)
% 0.39/0.63          | (r1_tarski @ X0 @ X2))),
% 0.39/0.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X0)
% 0.39/0.63          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.39/0.63          | ~ (v1_relat_1 @ sk_D))),
% 0.39/0.63      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.63  thf('13', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(cc1_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.63       ( v1_relat_1 @ C ) ))).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.63         ((v1_relat_1 @ X12)
% 0.39/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.63  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.39/0.63      inference('demod', [status(thm)], ['12', '15'])).
% 0.39/0.63  thf('17', plain,
% 0.39/0.63      (![X3 : $i, X5 : $i]:
% 0.39/0.63         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.39/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.63  thf(t13_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.39/0.63       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.39/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.39/0.63  thf('19', plain,
% 0.39/0.63      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.63         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.39/0.63          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.39/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.39/0.63      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.39/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.39/0.63          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ sk_D)
% 0.39/0.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.39/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['5', '20'])).
% 0.39/0.63  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.39/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.39/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.63  thf('24', plain, ($false), inference('demod', [status(thm)], ['4', '23'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.51/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
