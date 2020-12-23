%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EfvO1dVBKF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:30 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 118 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  438 ( 980 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t35_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k6_relset_1 @ sk_C_2 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( ( k6_relset_1 @ X36 @ X37 @ X34 @ X35 )
        = ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C_2 @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X21 @ X22 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X23 @ X24 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X28 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_C_2 @ sk_A @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X38 ) @ X39 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X40 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['4','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EfvO1dVBKF
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 863 iterations in 0.498s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(t35_relset_1, conjecture,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.76/0.96       ( m1_subset_1 @
% 0.76/0.96         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.76/0.96         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.76/0.96          ( m1_subset_1 @
% 0.76/0.96            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.76/0.96            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C_2 @ sk_A @ sk_B @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k6_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.76/0.96         (((k6_relset_1 @ X36 @ X37 @ X34 @ X35) = (k8_relat_1 @ X34 @ X35))
% 0.76/0.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k6_relset_1 @ sk_C_2 @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf(t116_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ B ) =>
% 0.76/0.96       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X21 : $i, X22 : $i]:
% 0.76/0.96         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X21 @ X22)) @ X21)
% 0.76/0.96          | ~ (v1_relat_1 @ X22))),
% 0.76/0.96      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t3_subset, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (![X15 : $i, X16 : $i]:
% 0.76/0.96         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf(t117_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i]:
% 0.76/0.96         ((r1_tarski @ (k8_relat_1 @ X23 @ X24) @ X24) | ~ (v1_relat_1 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.76/0.96  thf(t1_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.76/0.96       ( r1_tarski @ A @ C ) ))).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.96         (~ (r1_tarski @ X4 @ X5)
% 0.76/0.96          | ~ (r1_tarski @ X5 @ X6)
% 0.76/0.96          | (r1_tarski @ X4 @ X6))),
% 0.76/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X0)
% 0.76/0.96          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.76/0.96          | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.76/0.96          | ~ (v1_relat_1 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '11'])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(cc1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( v1_relat_1 @ C ) ))).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X25)
% 0.76/0.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['12', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      (![X15 : $i, X17 : $i]:
% 0.76/0.96         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.96  thf(dt_k1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k1_relset_1 @ X28 @ X29 @ X30) @ (k1_zfmisc_1 @ X28))
% 0.76/0.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ 
% 0.76/0.96          (k1_relset_1 @ sk_C_2 @ sk_A @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 0.76/0.96          (k1_zfmisc_1 @ sk_C_2))),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.96         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.76/0.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k1_relset_1 @ sk_C_2 @ sk_A @ (k8_relat_1 @ X0 @ sk_D))
% 0.76/0.96           = (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ 
% 0.76/0.96          (k1_zfmisc_1 @ sk_C_2))),
% 0.76/0.96      inference('demod', [status(thm)], ['20', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (![X15 : $i, X16 : $i]:
% 0.76/0.96         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C_2)),
% 0.76/0.96      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.96  thf(t11_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ C ) =>
% 0.76/0.96       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/0.96           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.76/0.96         (~ (r1_tarski @ (k1_relat_1 @ X38) @ X39)
% 0.76/0.96          | ~ (r1_tarski @ (k2_relat_1 @ X38) @ X40)
% 0.76/0.96          | (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.76/0.96          | ~ (v1_relat_1 @ X38))),
% 0.76/0.96      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 0.76/0.96          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 0.76/0.96          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.76/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((v1_relat_1 @ X25)
% 0.76/0.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.96  thf('31', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))),
% 0.76/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 0.76/0.96          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.76/0.96      inference('demod', [status(thm)], ['28', '31'])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ sk_D)
% 0.76/0.96          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X0))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '32'])).
% 0.76/0.96  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '34'])).
% 0.76/0.96  thf('36', plain, ($false), inference('demod', [status(thm)], ['4', '35'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
