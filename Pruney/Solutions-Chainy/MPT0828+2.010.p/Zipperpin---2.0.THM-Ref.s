%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PnyaFkE5pj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  98 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 ( 995 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['12','21'])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['30','33','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PnyaFkE5pj
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 80 iterations in 0.036s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(t31_relset_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.50         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.50           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.50          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.50            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.50              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.50        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.50         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t25_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.50             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.50               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X6)
% 0.21/0.50          | (r1_tarski @ (k1_relat_1 @ X7) @ (k1_relat_1 @ X6))
% 0.21/0.50          | ~ (r1_tarski @ X7 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ (k1_relat_1 @ sk_C))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(fc3_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('5', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('6', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X12)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6', '9'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.21/0.50        | ((k1_relat_1 @ sk_C) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k1_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X15))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, (((k1_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.50         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((sk_B) != (k1_relat_1 @ sk_C)))
% 0.21/0.50         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((sk_B) != (sk_B)))
% 0.21/0.50         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.50  thf('27', plain, ((((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.50       ~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X6)
% 0.21/0.50          | (r1_tarski @ (k2_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 0.21/0.50          | ~ (r1_tarski @ X7 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('38', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('40', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.21/0.50  thf('41', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '33', '40'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
