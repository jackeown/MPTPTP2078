%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C1KLczsSsW

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 108 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  452 (1056 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1
        = ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v4_relat_1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['16','17','24'])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['32','35','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C1KLczsSsW
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 44 iterations in 0.021s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(t31_relset_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.48         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.48           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.48          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.48            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.48              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.48        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.48         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.48         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.48  thf('4', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t25_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( v1_relat_1 @ B ) =>
% 0.22/0.48           ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.48               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X3)
% 0.22/0.48          | (r1_tarski @ (k1_relat_1 @ X4) @ (k1_relat_1 @ X3))
% 0.22/0.48          | ~ (r1_tarski @ X4 @ X3)
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.48        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ (k1_relat_1 @ sk_C))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.48  thf('8', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.48  thf(t71_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.48  thf('9', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(cc1_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( v1_relat_1 @ C ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.48         ((v1_relat_1 @ X9)
% 0.22/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.48  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf(t91_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X7 @ (k1_relat_1 @ X8))
% 0.22/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X8 @ X7)) = (X7))
% 0.22/0.48          | ~ (v1_relat_1 @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.48        | ((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)) = (sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(cc2_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.48         ((v4_relat_1 @ X12 @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.48  thf('20', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf(t209_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i]:
% 0.22/0.48         (((X1) = (k7_relat_1 @ X1 @ X2))
% 0.22/0.48          | ~ (v4_relat_1 @ X1 @ X2)
% 0.22/0.48          | ~ (v1_relat_1 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('24', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain, (((k1_relat_1 @ sk_C) = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['16', '17', '24'])).
% 0.22/0.48  thf('26', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '25'])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.48         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((sk_B) != (sk_B)))
% 0.22/0.48         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.48  thf('29', plain, ((((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.22/0.48       ~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.22/0.48  thf('32', plain, (~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.22/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.48  thf('36', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X3)
% 0.22/0.48          | (r1_tarski @ (k2_relat_1 @ X4) @ (k2_relat_1 @ X3))
% 0.22/0.48          | ~ (r1_tarski @ X4 @ X3)
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.48        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.48  thf('39', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.48  thf('40', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.48  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('43', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.48  thf('44', plain, ($false),
% 0.22/0.48      inference('demod', [status(thm)], ['32', '35', '43'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
