%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4K3ky5NZk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  345 ( 773 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,
    ( ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('31',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['20','23','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m4K3ky5NZk
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 20 iterations in 0.014s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(t30_relset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.47         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.47           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.47            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.47              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.47        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.47         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.47         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.20/0.47         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t25_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.47               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | (r1_tarski @ (k1_relat_1 @ X2) @ (k1_relat_1 @ X1))
% 0.20/0.47          | ~ (r1_tarski @ X2 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.47        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.47  thf('10', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf(t71_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf('11', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( v1_relat_1 @ C ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((v1_relat_1 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.47  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.47  thf('17', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.20/0.47       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, (~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.20/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | (r1_tarski @ (k2_relat_1 @ X2) @ (k2_relat_1 @ X1))
% 0.20/0.47          | ~ (r1_tarski @ X2 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.47        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('28', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.47  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('31', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '23', '31'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
