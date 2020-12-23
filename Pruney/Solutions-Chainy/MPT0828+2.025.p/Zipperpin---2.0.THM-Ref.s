%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08yAfKCo2n

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  415 (1013 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( B
            = ( k1_relset_1 @ B @ A @ C ) )
          & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( B
              = ( k1_relset_1 @ B @ A @ C ) )
            & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relset_1])).

thf('0',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X15 )
      | ( r1_tarski @ X14 @ ( k1_relset_1 @ X16 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['10','15','22'])).

thf('24',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X15 )
      | ( r1_tarski @ X14 @ ( k2_relset_1 @ X16 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('36',plain,(
    sk_B
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['27','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08yAfKCo2n
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 26 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t31_relset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.20/0.47         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.20/0.47            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.20/0.47  thf('0', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t30_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.47         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.47           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k6_relat_1 @ X14) @ X15)
% 0.20/0.47          | (r1_tarski @ X14 @ (k1_relset_1 @ X16 @ X17 @ X15))
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.47          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.20/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('6', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 0.20/0.47          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.47  thf('8', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.47  thf(t91_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X6 @ (k1_relat_1 @ X7))
% 0.20/0.47          | ((k1_relat_1 @ (k7_relat_1 @ X7 @ X6)) = (X6))
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.47        | ((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.47          | (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         ((v4_relat_1 @ X8 @ X9)
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.47  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf(t209_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.47       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((X4) = (k7_relat_1 @ X4 @ X5))
% 0.20/0.47          | ~ (v4_relat_1 @ X4 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('22', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (((k1_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '15', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.47        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k6_relat_1 @ X14) @ X15)
% 0.20/0.47          | (r1_tarski @ X14 @ (k2_relset_1 @ X16 @ X17 @ X15))
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.47          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf('34', plain, (((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.47       ~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf('36', plain, (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, (((sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['27', '36'])).
% 0.20/0.47  thf('38', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['23', '37'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
