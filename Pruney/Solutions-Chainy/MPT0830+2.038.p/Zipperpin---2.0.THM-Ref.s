%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8JIu28aFXV

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 ( 684 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['10','15'])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X24 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['4','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8JIu28aFXV
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:04:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 58 iterations in 0.044s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(t33_relset_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.46       ( m1_subset_1 @
% 0.19/0.46         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.19/0.46         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.46          ( m1_subset_1 @
% 0.19/0.46            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.19/0.46            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(redefinition_k5_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.19/0.46          | ((k5_relset_1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.46  thf(dt_k7_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.46         ((v5_relat_1 @ X15 @ X17)
% 0.19/0.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.46  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf(d19_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (v5_relat_1 @ X5 @ X6)
% 0.19/0.46          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.19/0.46          | ~ (v1_relat_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.46          | (v1_relat_1 @ X3)
% 0.19/0.46          | ~ (v1_relat_1 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf(fc6_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.46  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.19/0.46      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.46  thf(t99_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( r1_tarski @
% 0.19/0.46         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ 
% 0.19/0.46           (k2_relat_1 @ X13))
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.19/0.46  thf(t1_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.46       ( r1_tarski @ A @ C ) ))).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.46          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.46          | (r1_tarski @ X0 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)
% 0.19/0.46          | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '19'])).
% 0.19/0.46  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.19/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf(t87_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i]:
% 0.19/0.46         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.19/0.46          | ~ (v1_relat_1 @ X11))),
% 0.19/0.46      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.19/0.46  thf(t11_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.19/0.46           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.19/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ X24)
% 0.19/0.46          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.19/0.46          | ~ (v1_relat_1 @ X22))),
% 0.19/0.46      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.46          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.19/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.19/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.46  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.19/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ sk_D)
% 0.19/0.46          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '28'])).
% 0.19/0.46  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.46  thf('32', plain, ($false), inference('demod', [status(thm)], ['4', '31'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
